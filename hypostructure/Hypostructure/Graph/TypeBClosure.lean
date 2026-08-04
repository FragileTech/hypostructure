import Hypostructure.Graph.TypeBHybridLedger

/-!
# Direct Type B fan-window cycles: the alternatives that close the target

This file is the graph-mathematics content of the two *closing* alternatives of
manuscript node `[72]` (`typeBfan`) of `original_erdos_64_proof.tex`:

* `lem:typeB-direct-fan-window-cycles` -- the three same-window direct cycle
  eliminations, `hasCycleWithLength_of_sameWindowAttachment`,
  `hasCycleWithLength_of_crossWindowWedge` and
  `hasCycleWithLength_of_interlacedWindowPair`;
* `lem:typeB-two-window-cycles` -- `hasCycleWithLength_of_twoWindowPair`.

These are the only Type B alternatives that *close the dyadic cycle target*.
Everything else on the Type B branch either contradicts minimality through a
different lever or is a genuine retained residual; the closing/non-closing map
is recorded in the section `What does not close` at the end of the file, and the
non-closing cases are deliberately left open.

## Shape of the results

Each closure is stated twice.

* A *raw* form whose length hypothesis is exactly the length of the cycle that
  gets built, e.g. `LengthOK (b - a + 2)`.  This is the usable mathematics.
* A *dyadic* form carrying the manuscript's arithmetic side condition
  (`b - a ∈ {2, 6}`, `|x - y| ∈ {0, 4, 12}`, `L_× ∈ {8, 16}`,
  `|i - j| + |a - b| ∈ {0, 4, 12}`) together with `AcceptedLengths`, and a
  bundled `∀ witness, HasCycleWithLength LengthOK object` corollary -- the shape
  a `Core.Strategy.DichotomyData.closeLeft` / `closeRight` needs.

`AcceptedLengths` records that `4`, `8` and `16` are accepted cycle lengths.
Exactly like `TypeBOpenPorts.LocalHypotheses.fourAccepted`, this is a fact about
the *registered target predicate*, discharged once at the registration site (for
the EG target `4 = 2 ^ 2`, `8 = 2 ^ 3`, `16 = 2 ^ 4`); it is not a hypothesis
about the graph.

## What is assumed, and what is not

There is **no** hypothesis of the form "configuration `X` does not occur".  The
window data enters positively: `Window.IsPacked` asks only that consecutive
coordinates be adjacent and that the thirteen coordinates be distinct.  The
manuscript's standing side conditions -- "`u` and `v` lie outside `W`", "the
packed windows are vertex-disjoint" -- are statements about the *supplied*
vertices, in the same spirit as `DecoratedFan.Certificate.hub_not_mem_rim`, and
at profile level they are read off `TypeBFanClosedPorts.Profile.IsWindowIncidence`
rather than assumed.

Nothing here is redefined: the cycle target and its certificate are
`Graph.Target`, the ports and the high-neighbourhood normal form are
`Graph.TypeBOpenPorts`, the `P₁₃` coordinate algebra (`Index`, `gap`,
`IsDyadic`, `attachmentCycleLength`, `outsideCycleLength`, `IsLegal`,
`WedgeSafe`) is `Graph.TypeBMarkedFan`, and the assigned fan-window profile with
its two incidence kinds is `Graph.TypeBFanClosedPorts`.
-/

namespace Hypostructure.Graph.TypeBClosure

open Hypostructure.Graph
open Hypostructure.Graph.TypeBOpenPorts
open Hypostructure.Graph.TypeBMarkedFan
open Hypostructure.Graph.TypeBFanClosedPorts

universe u

variable {object : FiniteObject.{u}} {LengthOK : Nat → Prop}

/-! ## Accepted cycle lengths

The three lengths the direct Type B constructions produce. -/

/-- `4`, `8` and `16` are accepted cycle lengths.

This is a fact about the *registered target predicate*, discharged once at the
registration site -- for the EG dyadic target `4 = 2 ^ 2`, `8 = 2 ^ 3`,
`16 = 2 ^ 4` -- exactly as `TypeBOpenPorts.LocalHypotheses.fourAccepted` is.  It
says nothing about the graph. -/
structure AcceptedLengths (LengthOK : Nat → Prop) : Prop where
  /-- The four-cycle `2 ^ 2`. -/
  four : LengthOK 4
  /-- The eight-cycle `2 ^ 3`. -/
  eight : LengthOK 8
  /-- The sixteen-cycle `2 ^ 4`. -/
  sixteen : LengthOK 16

/-- The manuscript's own length predicate `Pow` accepts the three lengths. -/
theorem acceptedLengths_isDyadic : AcceptedLengths IsDyadic where
  four := ⟨2, rfl⟩
  eight := ⟨3, rfl⟩
  sixteen := ⟨4, rfl⟩

/-! ## The two cycle constructions

Both cycles built anywhere in this file come from one of the following two
shapes, which are the shapes drawn in the proof of
`lem:typeB-direct-fan-window-cycles`. -/

/-- `u p_a P p_b u`: one outside vertex closes a path segment into a cycle. -/
def attachmentCycle {segmentSource segmentTarget outside : object.Vertex}
    (segment : object.graph.Walk segmentSource segmentTarget)
    (enter : object.graph.Adj outside segmentSource)
    (close : object.graph.Adj segmentTarget outside) :
    object.graph.Walk outside outside :=
  SimpleGraph.Walk.cons enter
    (segment.append (SimpleGraph.Walk.cons close SimpleGraph.Walk.nil))

/-- The attachment cycle has length `|segment| + 2`. -/
theorem attachmentCycle_length {segmentSource segmentTarget outside : object.Vertex}
    (segment : object.graph.Walk segmentSource segmentTarget)
    (enter : object.graph.Adj outside segmentSource)
    (close : object.graph.Adj segmentTarget outside) :
    (attachmentCycle segment enter close).length = segment.length + 2 := by
  simp [attachmentCycle, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_append]

/-- The attachment walk is a simple cycle as soon as the segment is a path with
distinct endpoints and the outside vertex misses it. -/
theorem attachmentCycle_isCycle {segmentSource segmentTarget outside : object.Vertex}
    {segment : object.graph.Walk segmentSource segmentTarget}
    (enter : object.graph.Adj outside segmentSource)
    (close : object.graph.Adj segmentTarget outside)
    (path : segment.IsPath) (endsNe : segmentSource ≠ segmentTarget)
    (avoids : outside ∉ segment.support) :
    (attachmentCycle segment enter close).IsCycle := by
  have supportEq :
      (segment.append (SimpleGraph.Walk.cons close SimpleGraph.Walk.nil)).support
        = segment.support ++ [outside] := by
    rw [SimpleGraph.Walk.support_append]
    simp
  have edgesEq :
      (segment.append (SimpleGraph.Walk.cons close SimpleGraph.Walk.nil)).edges
        = segment.edges ++ [s(segmentTarget, outside)] := by
    rw [SimpleGraph.Walk.edges_append]
    simp
  rw [attachmentCycle, SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def, supportEq]
    refine List.Nodup.append ((SimpleGraph.Walk.isPath_def _).1 path) (by simp) ?_
    intro z left right
    rw [List.mem_singleton] at right
    exact avoids (right ▸ left)
  · rw [edgesEq]
    intro member
    rcases List.mem_append.1 member with inside | closing
    · exact avoids (SimpleGraph.Walk.fst_mem_support_of_mem_edges segment inside)
    · rw [List.mem_singleton] at closing
      rcases Sym2.eq_iff.1 closing with ⟨sameOutside, -⟩ | ⟨-, sameEnds⟩
      · exact avoids (sameOutside ▸ segment.end_mem_support)
      · exact endsNe sameEnds

/-- A directly validated attachment cycle, packaged as a cycle certificate. -/
def attachmentCertificate {segmentSource segmentTarget outside : object.Vertex}
    {segment : object.graph.Walk segmentSource segmentTarget}
    (enter : object.graph.Adj outside segmentSource)
    (close : object.graph.Adj segmentTarget outside)
    (path : segment.IsPath) (endsNe : segmentSource ≠ segmentTarget)
    (avoids : outside ∉ segment.support)
    (accepted : LengthOK (segment.length + 2)) :
    CycleCertificate object LengthOK where
  vertex := outside
  walk := attachmentCycle segment enter close
  isCycle := attachmentCycle_isCycle enter close path endsNe avoids
  length_ok := by
    rw [attachmentCycle_length]
    exact accepted

/-- `u S₁ v S₂ u`: two vertex-disjoint path segments closed by two outside
vertices.  All three of the manuscript's two-vertex direct cycles -- the fan
wedge `u h v p_y P p_x u`, the interlacing cycle
`u p_{a_u} P p_{a_v} v p_{b_v} P p_{b_u} u`, and the two-window cycle
`u p_i P p_j v q_b Q q_a u` -- are instances of this shape. -/
def crossCycle {firstSource firstTarget secondSource secondTarget base pivot :
      object.Vertex}
    (firstSegment : object.graph.Walk firstSource firstTarget)
    (secondSegment : object.graph.Walk secondSource secondTarget)
    (enter : object.graph.Adj base firstSource)
    (handoff : object.graph.Adj firstTarget pivot)
    (reenter : object.graph.Adj pivot secondSource)
    (close : object.graph.Adj secondTarget base) :
    object.graph.Walk base base :=
  SimpleGraph.Walk.cons enter
    (firstSegment.append
      (SimpleGraph.Walk.cons handoff
        (SimpleGraph.Walk.cons reenter
          (secondSegment.append
            (SimpleGraph.Walk.cons close SimpleGraph.Walk.nil)))))

/-- The cross cycle has length `|S₁| + |S₂| + 4`. -/
theorem crossCycle_length {firstSource firstTarget secondSource secondTarget
      base pivot : object.Vertex}
    (firstSegment : object.graph.Walk firstSource firstTarget)
    (secondSegment : object.graph.Walk secondSource secondTarget)
    (enter : object.graph.Adj base firstSource)
    (handoff : object.graph.Adj firstTarget pivot)
    (reenter : object.graph.Adj pivot secondSource)
    (close : object.graph.Adj secondTarget base) :
    (crossCycle firstSegment secondSegment enter handoff reenter close).length
      = firstSegment.length + secondSegment.length + 4 := by
  simp only [crossCycle, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_nil]
  omega

/-- The cross walk is a simple cycle when both segments are paths, they are
vertex-disjoint, and the two outside vertices are distinct and miss both
segments. -/
theorem crossCycle_isCycle {firstSource firstTarget secondSource secondTarget
      base pivot : object.Vertex}
    {firstSegment : object.graph.Walk firstSource firstTarget}
    {secondSegment : object.graph.Walk secondSource secondTarget}
    (enter : object.graph.Adj base firstSource)
    (handoff : object.graph.Adj firstTarget pivot)
    (reenter : object.graph.Adj pivot secondSource)
    (close : object.graph.Adj secondTarget base)
    (firstPath : firstSegment.IsPath) (secondPath : secondSegment.IsPath)
    (segmentsDisjoint :
      ∀ ⦃z : object.Vertex⦄, z ∈ firstSegment.support →
        z ∉ secondSegment.support)
    (baseNe : base ≠ pivot)
    (baseAvoidsFirst : base ∉ firstSegment.support)
    (baseAvoidsSecond : base ∉ secondSegment.support)
    (pivotAvoidsFirst : pivot ∉ firstSegment.support)
    (pivotAvoidsSecond : pivot ∉ secondSegment.support) :
    (crossCycle firstSegment secondSegment enter handoff reenter close).IsCycle := by
  have supportEq :
      (firstSegment.append
        (SimpleGraph.Walk.cons handoff
          (SimpleGraph.Walk.cons reenter
            (secondSegment.append
              (SimpleGraph.Walk.cons close SimpleGraph.Walk.nil))))).support
        = firstSegment.support ++ (pivot :: (secondSegment.support ++ [base])) := by
    rw [SimpleGraph.Walk.support_append]
    simp [SimpleGraph.Walk.support_append]
  have edgesEq :
      (firstSegment.append
        (SimpleGraph.Walk.cons handoff
          (SimpleGraph.Walk.cons reenter
            (secondSegment.append
              (SimpleGraph.Walk.cons close SimpleGraph.Walk.nil))))).edges
        = firstSegment.edges ++
            (s(firstTarget, pivot) :: s(pivot, secondSource) ::
              (secondSegment.edges ++ [s(secondTarget, base)])) := by
    rw [SimpleGraph.Walk.edges_append]
    simp [SimpleGraph.Walk.edges_append]
  rw [crossCycle, SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def, supportEq]
    refine List.Nodup.append ((SimpleGraph.Walk.isPath_def _).1 firstPath) ?_ ?_
    · refine List.nodup_cons.2 ⟨?_, ?_⟩
      · intro member
        rcases List.mem_append.1 member with inSecond | isBase
        · exact pivotAvoidsSecond inSecond
        · rw [List.mem_singleton] at isBase
          exact baseNe isBase.symm
      · refine List.Nodup.append ((SimpleGraph.Walk.isPath_def _).1 secondPath)
          (by simp) ?_
        intro z left right
        rw [List.mem_singleton] at right
        exact baseAvoidsSecond (right ▸ left)
    · intro z left right
      rcases List.mem_cons.1 right with isPivot | rest
      · exact pivotAvoidsFirst (isPivot ▸ left)
      rcases List.mem_append.1 rest with inSecond | isBase
      · exact segmentsDisjoint left inSecond
      · rw [List.mem_singleton] at isBase
        exact baseAvoidsFirst (isBase ▸ left)
  · rw [edgesEq]
    intro member
    rcases List.mem_append.1 member with inFirst | rest
    · exact baseAvoidsFirst
        (SimpleGraph.Walk.fst_mem_support_of_mem_edges firstSegment inFirst)
    rcases List.mem_cons.1 rest with handoffEdge | rest
    · rcases Sym2.eq_iff.1 handoffEdge with ⟨isTarget, -⟩ | ⟨isPivot, -⟩
      · exact baseAvoidsFirst (isTarget ▸ firstSegment.end_mem_support)
      · exact baseNe isPivot
    rcases List.mem_cons.1 rest with reenterEdge | rest
    · rcases Sym2.eq_iff.1 reenterEdge with ⟨isPivot, -⟩ | ⟨isSource, -⟩
      · exact baseNe isPivot
      · exact baseAvoidsSecond (isSource ▸ secondSegment.start_mem_support)
    rcases List.mem_append.1 rest with inSecond | closing
    · exact baseAvoidsSecond
        (SimpleGraph.Walk.fst_mem_support_of_mem_edges secondSegment inSecond)
    · rw [List.mem_singleton] at closing
      rcases Sym2.eq_iff.1 closing with ⟨isTarget, -⟩ | ⟨-, sourceIsTarget⟩
      · exact baseAvoidsSecond (isTarget ▸ secondSegment.end_mem_support)
      · exact segmentsDisjoint firstSegment.start_mem_support
          (sourceIsTarget ▸ secondSegment.end_mem_support)

/-- A directly validated cross cycle, packaged as a cycle certificate. -/
def crossCertificate {firstSource firstTarget secondSource secondTarget
      base pivot : object.Vertex}
    {firstSegment : object.graph.Walk firstSource firstTarget}
    {secondSegment : object.graph.Walk secondSource secondTarget}
    (enter : object.graph.Adj base firstSource)
    (handoff : object.graph.Adj firstTarget pivot)
    (reenter : object.graph.Adj pivot secondSource)
    (close : object.graph.Adj secondTarget base)
    (firstPath : firstSegment.IsPath) (secondPath : secondSegment.IsPath)
    (segmentsDisjoint :
      ∀ ⦃z : object.Vertex⦄, z ∈ firstSegment.support →
        z ∉ secondSegment.support)
    (baseNe : base ≠ pivot)
    (baseAvoidsFirst : base ∉ firstSegment.support)
    (baseAvoidsSecond : base ∉ secondSegment.support)
    (pivotAvoidsFirst : pivot ∉ firstSegment.support)
    (pivotAvoidsSecond : pivot ∉ secondSegment.support)
    (accepted : LengthOK (firstSegment.length + secondSegment.length + 4)) :
    CycleCertificate object LengthOK where
  vertex := base
  walk := crossCycle firstSegment secondSegment enter handoff reenter close
  isCycle := crossCycle_isCycle enter handoff reenter close firstPath secondPath
    segmentsDisjoint baseNe baseAvoidsFirst baseAvoidsSecond pivotAvoidsFirst
    pivotAvoidsSecond
  length_ok := by
    rw [crossCycle_length]
    exact accepted

/-! ## Packed `P₁₃` windows presented in the ambient graph -/

/-- The manuscript's packed induced window `P = p₀p₁⋯p₁₂`, presented in the
ambient graph by its coordinate map.  Pure data: there are no propositional
fields, and the two facts a window supplies are `IsPacked`. -/
structure Window (object : FiniteObject.{u}) where
  /-- `p_i`.  Only the coordinates `i ≤ 12` are ever used. -/
  coordinate : Nat → object.Vertex

/-- `P` really is a thirteen-vertex path of `G` in the displayed order.

Both clauses are positive facts about the supplied coordinates.  *Inducedness is
not required*: no construction below uses the absence of a chord, only the
displayed edges and the distinctness of the thirteen vertices. -/
structure Window.IsPacked (w : Window object) : Prop where
  /-- `p_i p_{i+1} ∈ E(G)` for `i < 12`. -/
  step : ∀ i, i < 12 → object.graph.Adj (w.coordinate i) (w.coordinate (i + 1))
  /-- The thirteen displayed vertices are pairwise distinct. -/
  distinct : ∀ i ≤ 12, ∀ j ≤ 12, w.coordinate i = w.coordinate j → i = j

namespace Window

variable {w : Window object}

/-- The forward stretch `p_i P p_{i+n}` of the window. -/
private theorem exists_forwardSegment (packed : w.IsPacked) (i : Nat) :
    ∀ n, i + n ≤ 12 →
      ∃ segment : object.graph.Walk (w.coordinate i) (w.coordinate (i + n)),
        segment.IsPath ∧ segment.length = n ∧
          ∀ z ∈ segment.support, ∃ t, t ≤ n ∧ z = w.coordinate (i + t) := by
  intro n
  induction n with
  | zero =>
      intro _
      refine ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, rfl, ?_⟩
      intro z member
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at member
      exact ⟨0, le_refl 0, member⟩
  | succ n induction =>
      intro bound
      obtain ⟨segment, path, length, member⟩ := induction (by omega)
      have adjacency :
          object.graph.Adj (w.coordinate (i + n)) (w.coordinate (i + n + 1)) :=
        packed.step (i + n) (by omega)
      have fresh : w.coordinate (i + n + 1) ∉ segment.support := by
        intro inside
        obtain ⟨t, small, equal⟩ := member _ inside
        have index := packed.distinct (i + n + 1) (by omega) (i + t) (by omega) equal
        omega
      have supportEq :
          (segment.append
            (SimpleGraph.Walk.cons adjacency SimpleGraph.Walk.nil)).support
            = segment.support ++ [w.coordinate (i + n + 1)] := by
        rw [SimpleGraph.Walk.support_append]
        simp
      refine ⟨segment.append (SimpleGraph.Walk.cons adjacency SimpleGraph.Walk.nil),
        ?_, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_def, supportEq]
        refine List.Nodup.append ((SimpleGraph.Walk.isPath_def _).1 path)
          (by simp) ?_
        intro z left right
        rw [List.mem_singleton] at right
        exact fresh (right ▸ left)
      · rw [SimpleGraph.Walk.length_append, length]
        simp
      · intro z inside
        rw [supportEq, List.mem_append] at inside
        rcases inside with old | new
        · obtain ⟨t, small, equal⟩ := member _ old
          exact ⟨t, by omega, equal⟩
        · rw [List.mem_singleton] at new
          exact ⟨n + 1, le_refl _, by rw [new, Nat.add_assoc]⟩

/-- The window stretch `p_i P p_j` between any two coordinates: a path of length
`|i - j|` all of whose vertices are window coordinates between `i` and `j`.
Both the length and the location of the support are needed downstream -- the
length gives the cycle length, the location gives the disjointness of two
stretches and the avoidance by the outside vertices. -/
theorem exists_stretch (packed : w.IsPacked) {i j : Nat}
    (sourceBound : i ≤ 12) (targetBound : j ≤ 12) :
    ∃ segment : object.graph.Walk (w.coordinate i) (w.coordinate j),
      segment.IsPath ∧ segment.length = max i j - min i j ∧
        ∀ z ∈ segment.support,
          ∃ t, min i j ≤ t ∧ t ≤ max i j ∧ z = w.coordinate t := by
  rcases Nat.le_total i j with order | order
  · obtain ⟨n, rfl⟩ : ∃ n, j = i + n := ⟨j - i, by omega⟩
    obtain ⟨segment, path, length, member⟩ :=
      exists_forwardSegment packed i n targetBound
    refine ⟨segment, path, by omega, ?_⟩
    intro z inside
    obtain ⟨t, small, equal⟩ := member _ inside
    exact ⟨i + t, by omega, by omega, equal⟩
  · obtain ⟨n, rfl⟩ : ∃ n, i = j + n := ⟨i - j, by omega⟩
    obtain ⟨segment, path, length, member⟩ :=
      exists_forwardSegment packed j n sourceBound
    refine ⟨segment.reverse, path.reverse, ?_, ?_⟩
    · rw [SimpleGraph.Walk.length_reverse, length]
      omega
    · intro z inside
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at inside
      obtain ⟨t, small, equal⟩ := member _ inside
      exact ⟨j + t, by omega, by omega, equal⟩

/-- A vertex outside the thirteen window coordinates misses every window
stretch. -/
theorem not_mem_support_of_outside {i j : Nat}
    {segment : object.graph.Walk (w.coordinate i) (w.coordinate j)}
    (member : ∀ z ∈ segment.support,
      ∃ t, min i j ≤ t ∧ t ≤ max i j ∧ z = w.coordinate t)
    (sourceBound : i ≤ 12) (targetBound : j ≤ 12)
    {vertex : object.Vertex} (outside : ∀ t ≤ 12, vertex ≠ w.coordinate t) :
    vertex ∉ segment.support := by
  intro inside
  obtain ⟨t, lower, upper, equal⟩ := member _ inside
  exact outside t (by omega) equal

end Window

/-! ## `lem:typeB-direct-fan-window-cycles` (a): the same-neighbour attachment

If a cubic-closed neighbour `u` of the fan centre is same-window supported at
`P` with closed label `S(u) = {a, b}`, then `u p_a P p_b u` is a simple cycle of
length `(b - a) + 2`. -/

/-- **`lem:typeB-direct-fan-window-cycles`, first display**, raw form.

A vertex outside the packed window attached at two distinct window coordinates
`a < b` closes the window stretch into a simple cycle of length `(b - a) + 2`. -/
theorem hasCycleWithLength_of_sameWindowAttachment
    {w : Window object} (packed : w.IsPacked)
    {outside : object.Vertex} {a b : Nat}
    (order : a < b) (bound : b ≤ 12)
    (windowFree : ∀ t ≤ 12, outside ≠ w.coordinate t)
    (lower : object.graph.Adj outside (w.coordinate a))
    (upper : object.graph.Adj outside (w.coordinate b))
    (accepted : LengthOK (b - a + 2)) :
    HasCycleWithLength LengthOK object := by
  obtain ⟨segment, path, length, member⟩ :=
    Window.exists_stretch packed (i := a) (j := b) (by omega) bound
  have avoids : outside ∉ segment.support :=
    Window.not_mem_support_of_outside member (by omega) bound
      windowFree
  have endsNe : w.coordinate a ≠ w.coordinate b := by
    intro equal
    exact absurd (packed.distinct a (by omega) b bound equal) (by omega)
  refine ⟨attachmentCertificate lower upper.symm path endsNe avoids ?_⟩
  rw [length]
  have rewrite : max a b - min a b = b - a := by omega
  rw [rewrite]
  exact accepted

/-- **`lem:typeB-direct-fan-window-cycles`, first display**, dyadic form.

`b - a ∈ {2, 6}` gives a cycle of length `4` or `8`. -/
theorem hasCycleWithLength_of_dyadicSameWindowAttachment
    (accepted : AcceptedLengths LengthOK)
    {w : Window object} (packed : w.IsPacked)
    {outside : object.Vertex} {a b : Nat}
    (order : a < b) (bound : b ≤ 12)
    (windowFree : ∀ t ≤ 12, outside ≠ w.coordinate t)
    (lower : object.graph.Adj outside (w.coordinate a))
    (upper : object.graph.Adj outside (w.coordinate b))
    (dyadicGap : b - a = 2 ∨ b - a = 6) :
    HasCycleWithLength LengthOK object := by
  refine hasCycleWithLength_of_sameWindowAttachment packed order bound windowFree
    lower upper ?_
  rcases dyadicGap with gap | gap <;> rw [gap]
  · exact accepted.four
  · exact accepted.eight

/-- The same statement in the manuscript's label algebra: an *illegal* closed
label closes the target.

`IsLegal {a, b}` is `gap ∉ {2, 6}`, and `attachmentCycleLength a b = gap + 2` is
the length of the cycle built here; `isDyadic_attachmentCycleLength_iff` is the
arithmetic step.  So a same-window supported cubic-closed neighbour whose closed
label is not legal hands the branch a power-of-two cycle. -/
theorem hasCycleWithLength_of_illegalLabel
    (accepted : AcceptedLengths LengthOK)
    {w : Window object} (packed : w.IsPacked)
    {outside : object.Vertex} {a b : Index} (distinct : a ≠ b)
    (lower : object.graph.Adj outside (w.coordinate a.val))
    (upper : object.graph.Adj outside (w.coordinate b.val))
    (windowFree : ∀ t ≤ 12, outside ≠ w.coordinate t)
    (illegal : ¬ IsLegal {a, b}) :
    HasCycleWithLength LengthOK object := by
  have gapValue : gap a b = 2 ∨ gap a b = 6 := by
    by_contra safe
    refine illegal ?_
    intro x xMem y yMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at xMem yMem
    have symmetry : gap b a = 2 ∨ gap b a = 6 ↔ gap a b = 2 ∨ gap a b = 6 := by
      rw [gap_comm b a]
    rcases xMem with rfl | rfl <;> rcases yMem with rfl | rfl
    · simp
    · omega
    · rw [gap_comm]; omega
    · simp
  rcases Nat.lt_trichotomy a.val b.val with order | order | order
  · refine hasCycleWithLength_of_dyadicSameWindowAttachment accepted packed order
      (by omega) windowFree lower upper ?_
    have : gap a b = b.val - a.val := by simp only [gap]; omega
    omega
  · exact absurd (Fin.ext order) distinct
  · refine hasCycleWithLength_of_dyadicSameWindowAttachment accepted packed order
      (by omega) windowFree upper lower ?_
    have : gap a b = a.val - b.val := by simp only [gap]; omega
    omega

/-! ## `lem:typeB-direct-fan-window-cycles` (b): the fan wedge across the hub

Two distinct cubic-closed neighbours `u, v` of the centre `h`, attached to the
same window at coordinates `x` and `y`, close the cycle `u h v p_y P p_x u` of
length `4 + |x - y|`. -/

/-- **`lem:typeB-direct-fan-window-cycles`, second display**, raw form. -/
theorem hasCycleWithLength_of_crossWindowWedge
    {w : Window object} (packed : w.IsPacked)
    {hub left right : object.Vertex} {x y : Nat}
    (sourceBound : x ≤ 12) (targetBound : y ≤ 12)
    (hubFree : ∀ t ≤ 12, hub ≠ w.coordinate t)
    (leftFree : ∀ t ≤ 12, left ≠ w.coordinate t)
    (rightFree : ∀ t ≤ 12, right ≠ w.coordinate t)
    (distinct : left ≠ right)
    (hubLeft : object.graph.Adj hub left) (hubRight : object.graph.Adj hub right)
    (leftWindow : object.graph.Adj left (w.coordinate x))
    (rightWindow : object.graph.Adj right (w.coordinate y))
    (accepted : LengthOK (4 + (max x y - min x y))) :
    HasCycleWithLength LengthOK object := by
  obtain ⟨segment, path, length, member⟩ :=
    Window.exists_stretch packed (i := y) (j := x) targetBound sourceBound
  have leftAvoids : left ∉ segment.support :=
    Window.not_mem_support_of_outside member targetBound
      sourceBound leftFree
  have rightAvoids : right ∉ segment.support :=
    Window.not_mem_support_of_outside member targetBound
      sourceBound rightFree
  have hubAvoids : hub ∉ segment.support :=
    Window.not_mem_support_of_outside member targetBound
      sourceBound hubFree
  refine ⟨crossCertificate (firstSegment := SimpleGraph.Walk.nil)
    (secondSegment := segment) hubLeft.symm hubRight rightWindow
    leftWindow.symm SimpleGraph.Walk.IsPath.nil path ?_ distinct ?_ leftAvoids
    ?_ rightAvoids ?_⟩
  · intro z inside
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at inside
    exact inside ▸ hubAvoids
  · rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
    exact hubLeft.ne'
  · rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
    exact hubRight.ne'
  · simp only [SimpleGraph.Walk.length_nil, length]
    have rewrite : 0 + (max y x - min y x) + 4 = 4 + (max x y - min x y) := by
      omega
    rw [rewrite]
    exact accepted

/-- **`lem:typeB-direct-fan-window-cycles`, second display**, dyadic form.

`|x - y| ∈ {0, 4, 12}` gives a cycle of length `4`, `8` or `16`. -/
theorem hasCycleWithLength_of_dyadicCrossWindowWedge
    (accepted : AcceptedLengths LengthOK)
    {w : Window object} (packed : w.IsPacked)
    {hub left right : object.Vertex} {x y : Nat}
    (sourceBound : x ≤ 12) (targetBound : y ≤ 12)
    (hubFree : ∀ t ≤ 12, hub ≠ w.coordinate t)
    (leftFree : ∀ t ≤ 12, left ≠ w.coordinate t)
    (rightFree : ∀ t ≤ 12, right ≠ w.coordinate t)
    (distinct : left ≠ right)
    (hubLeft : object.graph.Adj hub left) (hubRight : object.graph.Adj hub right)
    (leftWindow : object.graph.Adj left (w.coordinate x))
    (rightWindow : object.graph.Adj right (w.coordinate y))
    (dyadicGap : max x y - min x y = 0 ∨ max x y - min x y = 4 ∨
      max x y - min x y = 12) :
    HasCycleWithLength LengthOK object := by
  refine hasCycleWithLength_of_crossWindowWedge packed sourceBound targetBound
    hubFree leftFree rightFree distinct hubLeft hubRight leftWindow rightWindow ?_
  rcases dyadicGap with gap | gap | gap <;> rw [gap]
  · exact accepted.four
  · exact accepted.eight
  · exact accepted.sixteen

/-- The same statement in the manuscript's label algebra: two same-window
neighbours whose singleton labels are *not* `C₂`-compatible close the target.

`WedgeSafe {x} {y}` is `gap ∉ {0, 4, 12}` and `outsideCycleLength 2 x y`
is `4 + gap`, the length of the cycle built here.  This is the graph-side
content of the `C₂`-compatibility demanded by `def:marked-typeB-fan`: a
certificate-marked fan cannot violate it without handing over a power-of-two
cycle. -/
theorem hasCycleWithLength_of_notWedgeSafe
    (accepted : AcceptedLengths LengthOK)
    {w : Window object} (packed : w.IsPacked)
    {hub left right : object.Vertex} {x y : Index}
    (hubFree : ∀ t ≤ 12, hub ≠ w.coordinate t)
    (leftFree : ∀ t ≤ 12, left ≠ w.coordinate t)
    (rightFree : ∀ t ≤ 12, right ≠ w.coordinate t)
    (distinct : left ≠ right)
    (hubLeft : object.graph.Adj hub left) (hubRight : object.graph.Adj hub right)
    (leftWindow : object.graph.Adj left (w.coordinate x.val))
    (rightWindow : object.graph.Adj right (w.coordinate y.val))
    (notSafe : ¬ WedgeSafe {x} {y}) :
    HasCycleWithLength LengthOK object := by
  have gapValue : gap x y = 0 ∨ gap x y = 4 ∨ gap x y = 12 := by
    by_contra safe
    refine notSafe ?_
    rw [wedgeSafe_iff]
    intro a aMem b bMem
    rw [Finset.mem_singleton] at aMem bMem
    subst aMem; subst bMem
    tauto
  refine hasCycleWithLength_of_dyadicCrossWindowWedge accepted packed
    (by omega) (by omega) hubFree leftFree rightFree distinct hubLeft hubRight
    leftWindow rightWindow ?_
  simpa only [gap] using gapValue

/-! ## `lem:typeB-direct-fan-window-cycles` (c): the interlacing cycle

`a_u < a_v < b_u < b_v` gives `u p_{a_u} P p_{a_v} v p_{b_v} P p_{b_u} u`, of
length `L_×(u, v) = 4 + (a_v - a_u) + (b_v - b_u)`. -/

/-- **`lem:typeB-direct-fan-window-cycles`, third display**, raw form. -/
theorem hasCycleWithLength_of_interlacedWindowPair
    {w : Window object} (packed : w.IsPacked)
    {left right : object.Vertex} {leftLow rightLow leftHigh rightHigh : Nat}
    (interlaceOne : leftLow < rightLow) (interlaceTwo : rightLow < leftHigh)
    (interlaceThree : leftHigh < rightHigh) (bound : rightHigh ≤ 12)
    (leftFree : ∀ t ≤ 12, left ≠ w.coordinate t)
    (rightFree : ∀ t ≤ 12, right ≠ w.coordinate t)
    (distinct : left ≠ right)
    (leftLowEdge : object.graph.Adj left (w.coordinate leftLow))
    (leftHighEdge : object.graph.Adj left (w.coordinate leftHigh))
    (rightLowEdge : object.graph.Adj right (w.coordinate rightLow))
    (rightHighEdge : object.graph.Adj right (w.coordinate rightHigh))
    (accepted : LengthOK ((rightLow - leftLow) + (rightHigh - leftHigh) + 4)) :
    HasCycleWithLength LengthOK object := by
  obtain ⟨firstSegment, firstPath, firstLength, firstMember⟩ :=
    Window.exists_stretch packed (i := leftLow) (j := rightLow) (by omega) (by omega)
  obtain ⟨secondSegment, secondPath, secondLength, secondMember⟩ :=
    Window.exists_stretch packed (i := rightHigh) (j := leftHigh) bound (by omega)
  have segmentsDisjoint : ∀ ⦃z : object.Vertex⦄, z ∈ firstSegment.support →
      z ∉ secondSegment.support := by
    intro z inFirst inSecond
    obtain ⟨s, sLow, sHigh, sEq⟩ := firstMember _ inFirst
    obtain ⟨t, tLow, tHigh, tEq⟩ := secondMember _ inSecond
    have index := packed.distinct s (by omega) t (by omega) (sEq ▸ tEq ▸ rfl)
    omega
  refine ⟨crossCertificate leftLowEdge rightLowEdge.symm rightHighEdge
    leftHighEdge.symm firstPath secondPath segmentsDisjoint distinct ?_ ?_ ?_ ?_ ?_⟩
  · exact Window.not_mem_support_of_outside firstMember
      (by omega) (by omega) leftFree
  · exact Window.not_mem_support_of_outside secondMember
      bound (by omega) leftFree
  · exact Window.not_mem_support_of_outside firstMember
      (by omega) (by omega) rightFree
  · exact Window.not_mem_support_of_outside secondMember
      bound (by omega) rightFree
  · rw [firstLength, secondLength]
    have first : max leftLow rightLow - min leftLow rightLow
        = rightLow - leftLow := by omega
    have second : max rightHigh leftHigh - min rightHigh leftHigh
        = rightHigh - leftHigh := by omega
    rw [first, second]
    exact accepted

/-- **`lem:typeB-direct-fan-window-cycles`, third display**, dyadic form.

`L_× ∈ {8, 16}`, i.e. `(a_v - a_u) + (b_v - b_u) ∈ {4, 12}`. -/
theorem hasCycleWithLength_of_dyadicInterlacedWindowPair
    (accepted : AcceptedLengths LengthOK)
    {w : Window object} (packed : w.IsPacked)
    {left right : object.Vertex} {leftLow rightLow leftHigh rightHigh : Nat}
    (interlaceOne : leftLow < rightLow) (interlaceTwo : rightLow < leftHigh)
    (interlaceThree : leftHigh < rightHigh) (bound : rightHigh ≤ 12)
    (leftFree : ∀ t ≤ 12, left ≠ w.coordinate t)
    (rightFree : ∀ t ≤ 12, right ≠ w.coordinate t)
    (distinct : left ≠ right)
    (leftLowEdge : object.graph.Adj left (w.coordinate leftLow))
    (leftHighEdge : object.graph.Adj left (w.coordinate leftHigh))
    (rightLowEdge : object.graph.Adj right (w.coordinate rightLow))
    (rightHighEdge : object.graph.Adj right (w.coordinate rightHigh))
    (dyadicCross : (rightLow - leftLow) + (rightHigh - leftHigh) = 4 ∨
      (rightLow - leftLow) + (rightHigh - leftHigh) = 12) :
    HasCycleWithLength LengthOK object := by
  refine hasCycleWithLength_of_interlacedWindowPair packed interlaceOne
    interlaceTwo interlaceThree bound leftFree rightFree distinct leftLowEdge
    leftHighEdge rightLowEdge rightHighEdge ?_
  rcases dyadicCross with cross | cross <;> rw [cross]
  · exact accepted.eight
  · exact accepted.sixteen

/-! ## `lem:typeB-two-window-cycles`

Two distinct cubic-closed neighbours with incidences into two vertex-disjoint
packed windows close `u p_i P p_j v q_b Q q_a u`, of length
`4 + |i - j| + |a - b|`. -/

/-- **`lem:typeB-two-window-cycles`**, raw form. -/
theorem hasCycleWithLength_of_twoWindowPair
    {first second : Window object}
    (firstPacked : first.IsPacked) (secondPacked : second.IsPacked)
    (windowsDisjoint : ∀ s ≤ 12, ∀ t ≤ 12,
      first.coordinate s ≠ second.coordinate t)
    {left right : object.Vertex} {i j a b : Nat}
    (boundI : i ≤ 12) (boundJ : j ≤ 12) (boundA : a ≤ 12) (boundB : b ≤ 12)
    (leftFreeFirst : ∀ t ≤ 12, left ≠ first.coordinate t)
    (leftFreeSecond : ∀ t ≤ 12, left ≠ second.coordinate t)
    (rightFreeFirst : ∀ t ≤ 12, right ≠ first.coordinate t)
    (rightFreeSecond : ∀ t ≤ 12, right ≠ second.coordinate t)
    (distinct : left ≠ right)
    (leftFirstEdge : object.graph.Adj left (first.coordinate i))
    (rightFirstEdge : object.graph.Adj right (first.coordinate j))
    (leftSecondEdge : object.graph.Adj left (second.coordinate a))
    (rightSecondEdge : object.graph.Adj right (second.coordinate b))
    (accepted : LengthOK
      ((max i j - min i j) + (max a b - min a b) + 4)) :
    HasCycleWithLength LengthOK object := by
  obtain ⟨firstSegment, firstPath, firstLength, firstMember⟩ :=
    Window.exists_stretch firstPacked (i := i) (j := j) boundI boundJ
  obtain ⟨secondSegment, secondPath, secondLength, secondMember⟩ :=
    Window.exists_stretch secondPacked (i := b) (j := a) boundB boundA
  have segmentsDisjoint : ∀ ⦃z : object.Vertex⦄, z ∈ firstSegment.support →
      z ∉ secondSegment.support := by
    intro z inFirst inSecond
    obtain ⟨s, sLow, sHigh, sEq⟩ := firstMember _ inFirst
    obtain ⟨t, tLow, tHigh, tEq⟩ := secondMember _ inSecond
    exact windowsDisjoint s (by omega) t (by omega) (sEq ▸ tEq ▸ rfl)
  refine ⟨crossCertificate leftFirstEdge rightFirstEdge.symm rightSecondEdge
    leftSecondEdge.symm firstPath secondPath segmentsDisjoint distinct ?_ ?_ ?_
    ?_ ?_⟩
  · exact Window.not_mem_support_of_outside firstMember
      boundI boundJ leftFreeFirst
  · exact Window.not_mem_support_of_outside secondMember
      boundB boundA leftFreeSecond
  · exact Window.not_mem_support_of_outside firstMember
      boundI boundJ rightFreeFirst
  · exact Window.not_mem_support_of_outside secondMember
      boundB boundA rightFreeSecond
  · rw [firstLength, secondLength]
    have rewrite : max b a - min b a = max a b - min a b := by omega
    rw [rewrite]
    exact accepted

/-- **`lem:typeB-two-window-cycles`**, dyadic form:
`|i - j| + |a - b| ∈ {0, 4, 12}`. -/
theorem hasCycleWithLength_of_dyadicTwoWindowPair
    (accepted : AcceptedLengths LengthOK)
    {first second : Window object}
    (firstPacked : first.IsPacked) (secondPacked : second.IsPacked)
    (windowsDisjoint : ∀ s ≤ 12, ∀ t ≤ 12,
      first.coordinate s ≠ second.coordinate t)
    {left right : object.Vertex} {i j a b : Nat}
    (boundI : i ≤ 12) (boundJ : j ≤ 12) (boundA : a ≤ 12) (boundB : b ≤ 12)
    (leftFreeFirst : ∀ t ≤ 12, left ≠ first.coordinate t)
    (leftFreeSecond : ∀ t ≤ 12, left ≠ second.coordinate t)
    (rightFreeFirst : ∀ t ≤ 12, right ≠ first.coordinate t)
    (rightFreeSecond : ∀ t ≤ 12, right ≠ second.coordinate t)
    (distinct : left ≠ right)
    (leftFirstEdge : object.graph.Adj left (first.coordinate i))
    (rightFirstEdge : object.graph.Adj right (first.coordinate j))
    (leftSecondEdge : object.graph.Adj left (second.coordinate a))
    (rightSecondEdge : object.graph.Adj right (second.coordinate b))
    (dyadicSum : (max i j - min i j) + (max a b - min a b) = 0 ∨
      (max i j - min i j) + (max a b - min a b) = 4 ∨
      (max i j - min i j) + (max a b - min a b) = 12) :
    HasCycleWithLength LengthOK object := by
  refine hasCycleWithLength_of_twoWindowPair firstPacked secondPacked
    windowsDisjoint boundI boundJ boundA boundB leftFreeFirst leftFreeSecond
    rightFreeFirst rightFreeSecond distinct leftFirstEdge rightFirstEdge
    leftSecondEdge rightSecondEdge ?_
  rcases dyadicSum with sum | sum | sum <;> rw [sum]
  · exact accepted.four
  · exact accepted.eight
  · exact accepted.sixteen

/-! ## Reading the closures off an assigned fan-window profile

The manuscript's side conditions "`u ∉ W`" and "`u` is a cubic-closed neighbour
of `h`" are exactly `Profile.IsWindowIncidence` and
`Profile.closedNeighbours`; nothing has to be assumed about the graph.

The two alternatives that use the fan centre are spelled out below.  The
interlacing alternative (c) and the two-window alternative
`lem:typeB-two-window-cycles` need no fan datum at all -- their only side
condition is that the two neighbours lie outside the packed windows -- so
`window_free_of_not_mem_window` converts their `IsWindowIncidence` hypotheses in
one step, and no separate profile form is needed. -/

/-- Every vertex outside the packed-window union misses the thirteen displayed
coordinates of a window contained in that union. -/
theorem window_free_of_not_mem_window {profile : Profile object}
    {w : Window object} (inWindow : ∀ t ≤ 12, w.coordinate t ∈ profile.window)
    {vertex : object.Vertex} (outside : vertex ∉ profile.window) :
    ∀ t ≤ 12, vertex ≠ w.coordinate t := by
  intro t bound equal
  exact outside (equal ▸ inWindow t bound)

/-- **`lem:typeB-direct-fan-window-cycles`(a), profile form.**

A remainder-side fan neighbour with two window incidences into the same packed
window, at coordinates whose gap is `2` or `6`, hands the Type B branch a
power-of-two cycle.  `u ∉ W` is the first clause of
`Profile.IsWindowIncidence`, not a hypothesis. -/
theorem hasCycleWithLength_of_profileSameWindowAttachment
    (accepted : AcceptedLengths LengthOK)
    (profile : Profile object) {w : Window object} (packed : w.IsPacked)
    (inWindow : ∀ t ≤ 12, w.coordinate t ∈ profile.window)
    {neighbour : object.Vertex} {a b : Nat}
    (order : a < b) (bound : b ≤ 12)
    (lower : profile.IsWindowIncidence neighbour (w.coordinate a))
    (upper : profile.IsWindowIncidence neighbour (w.coordinate b))
    (dyadicGap : b - a = 2 ∨ b - a = 6) :
    HasCycleWithLength LengthOK object :=
  hasCycleWithLength_of_dyadicSameWindowAttachment accepted packed order bound
    (window_free_of_not_mem_window inWindow lower.1) lower.2.1 upper.2.1
    dyadicGap

/-- **`lem:typeB-direct-fan-window-cycles`(b), profile form.**

Two distinct cubic-closed neighbours of the fan centre with window incidences
into the same packed window, at coordinates whose gap is `0`, `4` or `12`, hand
the Type B branch a power-of-two cycle.

The hub's own separation from the packed-window union is the supplied
`hubOutside`: it is the manuscript's standing position of the fan centre against
its window envelope, the same kind of datum as
`DecoratedFan.Certificate.hub_not_mem_rim`.  The two edges `h u` and `h v` are
read off `Profile.closedNeighbours`, not assumed. -/
theorem hasCycleWithLength_of_profileCrossWindowWedge
    (accepted : AcceptedLengths LengthOK)
    (profile : Profile object) {w : Window object} (packed : w.IsPacked)
    (inWindow : ∀ t ≤ 12, w.coordinate t ∈ profile.window)
    (hubOutside : profile.marked.fan.hub ∉ profile.window)
    {left right : object.Vertex} {x y : Nat}
    (sourceBound : x ≤ 12) (targetBound : y ≤ 12)
    (leftClosed : left ∈ profile.closedNeighbours)
    (rightClosed : right ∈ profile.closedNeighbours)
    (distinct : left ≠ right)
    (leftIncidence : profile.IsWindowIncidence left (w.coordinate x))
    (rightIncidence : profile.IsWindowIncidence right (w.coordinate y))
    (dyadicGap : max x y - min x y = 0 ∨ max x y - min x y = 4 ∨
      max x y - min x y = 12) :
    HasCycleWithLength LengthOK object :=
  hasCycleWithLength_of_dyadicCrossWindowWedge accepted packed sourceBound
    targetBound (window_free_of_not_mem_window inWindow hubOutside)
    (window_free_of_not_mem_window inWindow leftIncidence.1)
    (window_free_of_not_mem_window inWindow rightIncidence.1) distinct
    (Profile.hub_adj_of_mem_closedNeighbours leftClosed)
    (Profile.hub_adj_of_mem_closedNeighbours rightClosed)
    leftIncidence.2.1 rightIncidence.2.1 dyadicGap

/-! ## The `closeLeft` / `closeRight` shapes

Each closing alternative, bundled as a single branch witness.  These are the
statements a registration consumes: `∀ witness, HasCycleWithLength LengthOK
object`, with the accepted lengths discharged at the registration site. -/

/-- Branch witness for `lem:typeB-direct-fan-window-cycles`(a): a packed window,
a vertex outside it, and two attachment coordinates at gap `2` or `6`. -/
def SameWindowAttachmentWitness (object : FiniteObject.{u}) : Prop :=
  ∃ (w : Window object) (outside : object.Vertex) (a b : Nat),
    w.IsPacked ∧ a < b ∧ b ≤ 12 ∧ (∀ t ≤ 12, outside ≠ w.coordinate t) ∧
      object.graph.Adj outside (w.coordinate a) ∧
      object.graph.Adj outside (w.coordinate b) ∧ (b - a = 2 ∨ b - a = 6)

/-- Branch witness for `lem:typeB-direct-fan-window-cycles`(b): a packed window,
a centre with two distinct neighbours outside the window, attached to it at gap
`0`, `4` or `12`. -/
def CrossWindowWedgeWitness (object : FiniteObject.{u}) : Prop :=
  ∃ (w : Window object) (hub left right : object.Vertex) (x y : Nat),
    w.IsPacked ∧ x ≤ 12 ∧ y ≤ 12 ∧
      (∀ t ≤ 12, hub ≠ w.coordinate t) ∧
      (∀ t ≤ 12, left ≠ w.coordinate t) ∧
      (∀ t ≤ 12, right ≠ w.coordinate t) ∧ left ≠ right ∧
      object.graph.Adj hub left ∧ object.graph.Adj hub right ∧
      object.graph.Adj left (w.coordinate x) ∧
      object.graph.Adj right (w.coordinate y) ∧
      (max x y - min x y = 0 ∨ max x y - min x y = 4 ∨
        max x y - min x y = 12)

/-- Branch witness for `lem:typeB-direct-fan-window-cycles`(c): two vertices
outside a packed window with interlacing attachment coordinates and
`L_× ∈ {8, 16}`. -/
def InterlacedWindowPairWitness (object : FiniteObject.{u}) : Prop :=
  ∃ (w : Window object) (left right : object.Vertex)
    (leftLow rightLow leftHigh rightHigh : Nat),
    w.IsPacked ∧ leftLow < rightLow ∧ rightLow < leftHigh ∧
      leftHigh < rightHigh ∧ rightHigh ≤ 12 ∧
      (∀ t ≤ 12, left ≠ w.coordinate t) ∧
      (∀ t ≤ 12, right ≠ w.coordinate t) ∧ left ≠ right ∧
      object.graph.Adj left (w.coordinate leftLow) ∧
      object.graph.Adj left (w.coordinate leftHigh) ∧
      object.graph.Adj right (w.coordinate rightLow) ∧
      object.graph.Adj right (w.coordinate rightHigh) ∧
      ((rightLow - leftLow) + (rightHigh - leftHigh) = 4 ∨
        (rightLow - leftLow) + (rightHigh - leftHigh) = 12)

/-- Branch witness for `lem:typeB-two-window-cycles`: two vertex-disjoint packed
windows and two outside vertices with `|i - j| + |a - b| ∈ {0, 4, 12}`. -/
def TwoWindowPairWitness (object : FiniteObject.{u}) : Prop :=
  ∃ (first second : Window object) (left right : object.Vertex) (i j a b : Nat),
    first.IsPacked ∧ second.IsPacked ∧
      (∀ s ≤ 12, ∀ t ≤ 12, first.coordinate s ≠ second.coordinate t) ∧
      i ≤ 12 ∧ j ≤ 12 ∧ a ≤ 12 ∧ b ≤ 12 ∧
      (∀ t ≤ 12, left ≠ first.coordinate t) ∧
      (∀ t ≤ 12, left ≠ second.coordinate t) ∧
      (∀ t ≤ 12, right ≠ first.coordinate t) ∧
      (∀ t ≤ 12, right ≠ second.coordinate t) ∧ left ≠ right ∧
      object.graph.Adj left (first.coordinate i) ∧
      object.graph.Adj right (first.coordinate j) ∧
      object.graph.Adj left (second.coordinate a) ∧
      object.graph.Adj right (second.coordinate b) ∧
      ((max i j - min i j) + (max a b - min a b) = 0 ∨
        (max i j - min i j) + (max a b - min a b) = 4 ∨
        (max i j - min i j) + (max a b - min a b) = 12)

/-- `closeLeft`/`closeRight` shape for the same-window attachment alternative. -/
theorem hasCycleWithLength_of_sameWindowAttachmentWitness
    (accepted : AcceptedLengths LengthOK) :
    SameWindowAttachmentWitness object → HasCycleWithLength LengthOK object := by
  rintro ⟨w, outside, a, b, packed, order, bound, free, lower, upper, dyadic⟩
  exact hasCycleWithLength_of_dyadicSameWindowAttachment accepted packed order
    bound free lower upper dyadic

/-- `closeLeft`/`closeRight` shape for the fan-wedge alternative. -/
theorem hasCycleWithLength_of_crossWindowWedgeWitness
    (accepted : AcceptedLengths LengthOK) :
    CrossWindowWedgeWitness object → HasCycleWithLength LengthOK object := by
  rintro ⟨w, hub, left, right, x, y, packed, boundX, boundY, hubFree, leftFree,
    rightFree, distinct, hubLeft, hubRight, leftWindow, rightWindow, dyadic⟩
  exact hasCycleWithLength_of_dyadicCrossWindowWedge accepted packed boundX
    boundY hubFree leftFree rightFree distinct hubLeft hubRight leftWindow
    rightWindow dyadic

/-- `closeLeft`/`closeRight` shape for the interlacing alternative. -/
theorem hasCycleWithLength_of_interlacedWindowPairWitness
    (accepted : AcceptedLengths LengthOK) :
    InterlacedWindowPairWitness object → HasCycleWithLength LengthOK object := by
  rintro ⟨w, left, right, leftLow, rightLow, leftHigh, rightHigh, packed, one,
    two, three, bound, leftFree, rightFree, distinct, leftLowEdge, leftHighEdge,
    rightLowEdge, rightHighEdge, dyadic⟩
  exact hasCycleWithLength_of_dyadicInterlacedWindowPair accepted packed one two
    three bound leftFree rightFree distinct leftLowEdge leftHighEdge
    rightLowEdge rightHighEdge dyadic

/-- `closeLeft`/`closeRight` shape for the two-window alternative. -/
theorem hasCycleWithLength_of_twoWindowPairWitness
    (accepted : AcceptedLengths LengthOK) :
    TwoWindowPairWitness object → HasCycleWithLength LengthOK object := by
  rintro ⟨first, second, left, right, i, j, a, b, firstPacked, secondPacked,
    windowsDisjoint, boundI, boundJ, boundA, boundB, leftFreeFirst,
    leftFreeSecond, rightFreeFirst, rightFreeSecond, distinct, leftFirstEdge,
    rightFirstEdge, leftSecondEdge, rightSecondEdge, dyadic⟩
  exact hasCycleWithLength_of_dyadicTwoWindowPair accepted firstPacked
    secondPacked windowsDisjoint boundI boundJ boundA boundB leftFreeFirst
    leftFreeSecond rightFreeFirst rightFreeSecond distinct leftFirstEdge
    rightFirstEdge leftSecondEdge rightSecondEdge dyadic

/-! ## `def:direct-cycle-free-closed-pair`: the node-`[72]` removal

Manuscript node `[72]` (`typeBfan`) is credited with
`def:closed-fan-window-pair`, `def:direct-cycle-free-closed-pair`,
`lem:typeB-direct-fan-window-cycles` and `lem:typeB-two-window-cycles`, with the
effect "removes direct fan-window and two-window cycle configurations *before*
the incidence payment".

The removal is a two-sided alternative on the assigned fan-window data.

* One side exhibits a direct configuration.  By the four theorems above it
  produces a power-of-two cycle, so it **closes the target**.
* The other side is `def:direct-cycle-free-closed-pair`: none of the direct
  configurations occurs.  This is verbatim the standing hypothesis of the
  incidence payment -- `lem:typeB-hybrid-incidence-budget` opens with "Suppose
  that none of the direct-cycle conclusions of
  `lem:typeB-direct-fan-window-cycles`, `lem:typeB-two-window-cycles` occurs" --
  and it is the class that continues to B1.

`DirectCycleConfiguration` collects exactly the four configurations, matched
clause by clause against `def:direct-cycle-free-closed-pair`:

* clause (a), `b_u - a_u ∈ {2, 6}`, is `SameWindowAttachmentWitness`;
* clause (b), `|x - y| ∈ {0, 4, 12}`, is `CrossWindowWedgeWitness`;
* clause (c), `L_×(u, v) ∈ {8, 16}`, is `InterlacedWindowPairWitness`;
* the two-window exclusion `|i - j| + |a - b| ∈ {0, 4, 12}` of
  `lem:typeB-two-window-cycles` is `TwoWindowPairWitness`.

No hypothesis is introduced by either side: the alternative is excluded middle
on one statement about the object. -/

/-- A direct fan-window or two-window cycle configuration: one of the three
same-window alternatives of `lem:typeB-direct-fan-window-cycles` or the
two-window alternative of `lem:typeB-two-window-cycles`. -/
def DirectCycleConfiguration (object : FiniteObject.{u}) : Prop :=
  SameWindowAttachmentWitness object ∨ CrossWindowWedgeWitness object ∨
    InterlacedWindowPairWitness object ∨ TwoWindowPairWitness object

/-- **`def:direct-cycle-free-closed-pair`**, read on the whole object: no closed
fan-window pair and no two-window closed pair violates the arithmetic
conditions, i.e. none of the direct-cycle conclusions of
`lem:typeB-direct-fan-window-cycles` or `lem:typeB-two-window-cycles` occurs.
This is the class that survives node `[72]` and enters the incidence payment. -/
def DirectCycleFree (object : FiniteObject.{u}) : Prop :=
  ¬ DirectCycleConfiguration object

/-- **`lem:typeB-direct-fan-window-cycles` together with
`lem:typeB-two-window-cycles`**: every direct configuration hands the Type B
branch a power-of-two cycle.

This is the `closeLeft`/`closeRight` fact of node `[72]`: the whole closing
content of the removal, with the accepted lengths discharged at the
registration site. -/
theorem hasCycleWithLength_of_directCycleConfiguration
    (accepted : AcceptedLengths LengthOK)
    (configuration : DirectCycleConfiguration object) :
    HasCycleWithLength LengthOK object := by
  rcases configuration with witness | witness | witness | witness
  · exact hasCycleWithLength_of_sameWindowAttachmentWitness accepted witness
  · exact hasCycleWithLength_of_crossWindowWedgeWitness accepted witness
  · exact hasCycleWithLength_of_interlacedWindowPairWitness accepted witness
  · exact hasCycleWithLength_of_twoWindowPairWitness accepted witness

/-- The node-`[72]` removal is exhaustive.  Nothing beyond excluded middle on a
single statement about the object is used, so the alternative introduces no
hypothesis. -/
theorem directCycleConfiguration_or_directCycleFree
    (object : FiniteObject.{u}) :
    DirectCycleConfiguration object ∨ DirectCycleFree object :=
  Classical.em _

/-! ## What does not close

The four theorems above are the *whole* closing content of the Type B branch.
The remaining Type B alternatives are recorded here, with the reason each one is
not a target closure.  Nothing below is proved to close, and nothing below is
given a manufactured closure.

* **Triangular ports and triangular fan cores** (`def:heavy-center-triangular-port`,
  `def:triangular-fan-core`, `lem:heavy-center-triangular-alternative`,
  `cor:heavy-center-local-dichotomy`, `cor:degree-four-local-activation`).  The
  cycle a triangular port supplies is the triangle `x a_p b_p x`, of length
  three.  `three_not_dyadic` below records that three is not an accepted length,
  and `exists_triangleCycle_of_isTriangular` records that three is exactly what
  is available.  This branch therefore *cannot* close the dyadic target; in the
  manuscript it routes into the fan ledger instead.
* **Fan-compatible open pairs and fan-closed ports**
  (`lem:compatible-pair-fan-closure`, `prop:fan-closed-port-typeB-routing`,
  `cor:compatible-pair-typeB-routing`).  These produce the *deficit bound*
  `D_B ≥ (k-3)/4 > 0` (`TypeBFanClosedPorts.fanClosedPortTypeBRouting`), an
  accounting statement.  No cycle is produced, so nothing closes.
* **The hybrid B1 ledger** (`lem:typeB-hybrid-incidence-budget`,
  `lem:typeB-hybrid-B1`, `TypeBHybridLedger.typeBHybridB1`).  Also accounting:
  it *pays* a positive-deficit fan, it does not hit the target.
* **The target-defect, compression and delocalization alternatives** inside B1
  (`def:typeB-multiclosed-residual`: "a Mersenne return, a target-defective
  quotient, a target-complete compression, or a proper/global delocalization").
  These contradict *minimality* through hereditary target-uncompressibility
  (invariant 8, `cor:uncompressible`) and the replacement lemma -- a different
  lever from the cycle target.  They are not power-of-two cycles and are not
  formalised here.
* **Fan-certificate residual centres** (`def:marked-typeB-fan`, clause (d) of
  `prop:fan-closed-port-typeB-routing`; the right-hand side of node `[71]`).
  Genuine residual: the centre carries no certificate labelling and is charged
  to the Type B fan-mass ledger.  It closes nothing.
* **B2 disjoint-carrier failure** (`def:typeB-bridge-statements` (ii),
  `lem:typeB-bridge-to-overlap`; the right-hand side of node `[72]`).  Genuine
  residual: a minimal Type B overlap obstruction.  It closes nothing.
* **Grouped decorated Type B envelopes whose envelope ledger cannot be closed**
  (`def:typeB-bridge-statements` (iii)).  Genuine residual.
* **Route-8 cores** (`lem:decorated-envelope-with-route8-core`,
  `lem:typeB-bridge-with-route8-core`).  Genuine residual, extracted into the
  Type A deficit ledger.  `thm:branch-kill` is explicitly stated *outside*
  route 8, so this one must stay open. -/

/-- Three is not a power of two.  This is why the triangular Type B alternative
cannot close the dyadic cycle target. -/
theorem three_not_dyadic : ¬ IsDyadic 3 := by
  intro dyadic
  rw [isDyadic_iff_of_le_sixteen (by omega)] at dyadic
  omega

/-- The triangular alternative supplies exactly a three-cycle.

The chord `a_p b_p` of a triangular port, together with the two port incidences,
is a simple cycle of length three -- and by `three_not_dyadic` three is not an
accepted length, so this alternative is *not* a closure.  It is recorded here so
that the boundary between the closing and non-closing Type B alternatives is
explicit rather than asserted. -/
theorem exists_triangleCycle_of_isTriangular {p : Port object}
    (triangular : p.IsTriangular) :
    ∃ (base : object.Vertex) (cycle : object.graph.Walk base base),
      cycle.IsCycle ∧ cycle.length = 3 := by
  obtain ⟨leftShoulder, leftMember, rightShoulder, rightMember, chord⟩ := triangular
  have leftEdge : object.graph.Adj p.endpoint leftShoulder :=
    Port.shoulder_adj leftMember
  have rightEdge : object.graph.Adj rightShoulder p.endpoint :=
    (Port.shoulder_adj rightMember).symm
  have path :
      (SimpleGraph.Walk.cons chord SimpleGraph.Walk.nil).IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [chord.ne]
  have avoids : p.endpoint ∉
      (SimpleGraph.Walk.cons chord SimpleGraph.Walk.nil).support := by
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false]
    intro member
    rcases member with equal | equal
    · exact leftEdge.ne equal
    · exact rightEdge.ne' equal
  refine ⟨p.endpoint,
    attachmentCycle (SimpleGraph.Walk.cons chord SimpleGraph.Walk.nil) leftEdge
      rightEdge,
    attachmentCycle_isCycle leftEdge rightEdge path chord.ne avoids, ?_⟩
  rw [attachmentCycle_length]
  simp

/-! ## Non-vacuity

Every hypothesis of the four closures is realised simultaneously by one explicit
finite graph: two vertex-disjoint packed `P₁₃` windows `P` and `Q`, two vertices
`u`, `v` outside both, and a centre `h` joined to `u` and `v`.  The attachments
are chosen so that all four manuscript alternatives fire at once, and each one
produces a cycle of a definite power-of-two length -- `8` in every case, so no
closure below is attained by a degenerate `4`-cycle. -/

namespace Witness

/-- Generating relation of the witness.  Vertices `0, …, 12` carry the packed
window `P`, vertices `13, …, 25` carry the packed window `Q`, `26 = u` and
`27 = v` are the two outside vertices, and `28 = h` is the fan centre. -/
def rel (left right : Fin 29) : Prop :=
  (left.val < 12 ∧ right.val = left.val + 1) ∨
    (13 ≤ left.val ∧ left.val < 25 ∧ right.val = left.val + 1) ∨
    (left.val = 26 ∧ (right.val = 0 ∨ right.val = 6 ∨ right.val = 13)) ∨
    (left.val = 27 ∧ (right.val = 2 ∨ right.val = 8 ∨ right.val = 15)) ∨
    (left.val = 28 ∧ (right.val = 26 ∨ right.val = 27))

instance decidableRel (left right : Fin 29) : Decidable (rel left right) := by
  unfold rel; infer_instance

/-- The witness graph. -/
def windowObject : FiniteObject where
  Vertex := Fin 29
  graph := SimpleGraph.fromRel rel
  vertices := inferInstance
  decideAdj := by
    intro left right
    simp only [SimpleGraph.fromRel_adj]
    infer_instance

local instance vertexDecEq : DecidableEq windowObject.Vertex :=
  inferInstanceAs (DecidableEq (Fin 29))

local instance adjDecidable : DecidableRel windowObject.graph.Adj :=
  windowObject.decideAdj

/-- The packed window `P = p₀⋯p₁₂` on the vertices `0, …, 12`. -/
def firstWindow : Window windowObject where
  coordinate := fun k => ⟨min k 12, by omega⟩

/-- The packed window `Q = q₀⋯q₁₂` on the vertices `13, …, 25`. -/
def secondWindow : Window windowObject where
  coordinate := fun k => ⟨13 + min k 12, by omega⟩

/-- The outside vertex `u`, attached to `p₀`, `p₆` and `q₀`. -/
def outsideLeft : windowObject.Vertex := ⟨26, by omega⟩

/-- The outside vertex `v`, attached to `p₂`, `p₈` and `q₂`. -/
def outsideRight : windowObject.Vertex := ⟨27, by omega⟩

/-- The fan centre `h`, joined to `u` and `v`. -/
def centre : windowObject.Vertex := ⟨28, by omega⟩

theorem firstWindow_packed : firstWindow.IsPacked (object := windowObject) where
  step := by
    intro i bound
    interval_cases i <;> decide
  distinct := by
    intro i boundI j boundJ equal
    have valEq : min i 12 = min j 12 := congrArg Fin.val equal
    omega

theorem secondWindow_packed : secondWindow.IsPacked (object := windowObject) where
  step := by
    intro i bound
    interval_cases i <;> decide
  distinct := by
    intro i boundI j boundJ equal
    have valEq : 13 + min i 12 = 13 + min j 12 := congrArg Fin.val equal
    omega

theorem windows_disjoint : ∀ s ≤ 12, ∀ t ≤ 12,
    (firstWindow.coordinate s : windowObject.Vertex)
      ≠ secondWindow.coordinate t := by
  intro s boundS t boundT equal
  have valEq : min s 12 = 13 + min t 12 := congrArg Fin.val equal
  omega

theorem outsideLeft_free_first :
    ∀ t ≤ 12, outsideLeft ≠ firstWindow.coordinate t := by
  intro t bound equal
  have valEq : (26 : Nat) = min t 12 := congrArg Fin.val equal
  omega

theorem outsideLeft_free_second :
    ∀ t ≤ 12, outsideLeft ≠ secondWindow.coordinate t := by
  intro t bound equal
  have valEq : (26 : Nat) = 13 + min t 12 := congrArg Fin.val equal
  omega

theorem outsideRight_free_first :
    ∀ t ≤ 12, outsideRight ≠ firstWindow.coordinate t := by
  intro t bound equal
  have valEq : (27 : Nat) = min t 12 := congrArg Fin.val equal
  omega

theorem outsideRight_free_second :
    ∀ t ≤ 12, outsideRight ≠ secondWindow.coordinate t := by
  intro t bound equal
  have valEq : (27 : Nat) = 13 + min t 12 := congrArg Fin.val equal
  omega

theorem centre_free_first : ∀ t ≤ 12, centre ≠ firstWindow.coordinate t := by
  intro t bound equal
  have valEq : (28 : Nat) = min t 12 := congrArg Fin.val equal
  omega

theorem outsideLeft_ne_outsideRight : outsideLeft ≠ outsideRight := by decide

theorem adj_left_p0 :
    windowObject.graph.Adj outsideLeft (firstWindow.coordinate 0) := by decide

theorem adj_left_p6 :
    windowObject.graph.Adj outsideLeft (firstWindow.coordinate 6) := by decide

theorem adj_left_q0 :
    windowObject.graph.Adj outsideLeft (secondWindow.coordinate 0) := by decide

theorem adj_right_p2 :
    windowObject.graph.Adj outsideRight (firstWindow.coordinate 2) := by decide

theorem adj_right_p8 :
    windowObject.graph.Adj outsideRight (firstWindow.coordinate 8) := by decide

theorem adj_right_q2 :
    windowObject.graph.Adj outsideRight (secondWindow.coordinate 2) := by decide

theorem adj_centre_left : windowObject.graph.Adj centre outsideLeft := by decide

theorem adj_centre_right : windowObject.graph.Adj centre outsideRight := by decide

/-- The predicate accepting exactly the three lengths the direct Type B
constructions produce.  It accepts no length below four, so nothing below is a
degenerate closure. -/
def dyadicLength (length : Nat) : Prop :=
  length = 4 ∨ length = 8 ∨ length = 16

theorem accepted : AcceptedLengths dyadicLength where
  four := Or.inl rfl
  eight := Or.inr (Or.inl rfl)
  sixteen := Or.inr (Or.inr rfl)

/-- `lem:typeB-direct-fan-window-cycles`(a) fires: `u` is attached at `p₀` and
`p₆`, a gap of six, so the window closes into an eight-cycle. -/
theorem sameWindowAttachment_fires :
    HasCycleWithLength (fun length => length = 8) windowObject :=
  hasCycleWithLength_of_sameWindowAttachment firstWindow_packed
    (a := 0) (b := 6) (by omega) (by omega) outsideLeft_free_first
    adj_left_p0 adj_left_p6 rfl

/-- `lem:typeB-direct-fan-window-cycles`(b) fires: `u` sits at `p₆` and `v` at
`p₂`, a gap of four, so `u h v p₂ P p₆ u` is an eight-cycle. -/
theorem crossWindowWedge_fires :
    HasCycleWithLength (fun length => length = 8) windowObject :=
  hasCycleWithLength_of_crossWindowWedge firstWindow_packed
    (x := 6) (y := 2) (by omega) (by omega) centre_free_first
    outsideLeft_free_first outsideRight_free_first outsideLeft_ne_outsideRight
    adj_centre_left adj_centre_right adj_left_p6 adj_right_p2 rfl

/-- `lem:typeB-direct-fan-window-cycles`(c) fires: the attachments `0 < 2 < 6 < 8`
interlace with `L_× = 4 + 2 + 2 = 8`. -/
theorem interlacedWindowPair_fires :
    HasCycleWithLength (fun length => length = 8) windowObject :=
  hasCycleWithLength_of_interlacedWindowPair firstWindow_packed
    (leftLow := 0) (rightLow := 2) (leftHigh := 6) (rightHigh := 8)
    (by omega) (by omega) (by omega) (by omega) outsideLeft_free_first
    outsideRight_free_first outsideLeft_ne_outsideRight adj_left_p0 adj_left_p6
    adj_right_p2 adj_right_p8 rfl

/-- `lem:typeB-two-window-cycles` fires: `|0 - 2| + |0 - 2| = 4`, so
`u p₀ P p₂ v q₂ Q q₀ u` is an eight-cycle. -/
theorem twoWindowPair_fires :
    HasCycleWithLength (fun length => length = 8) windowObject :=
  hasCycleWithLength_of_twoWindowPair firstWindow_packed secondWindow_packed
    windows_disjoint (i := 0) (j := 2) (a := 0) (b := 2) (by omega) (by omega)
    (by omega) (by omega) outsideLeft_free_first outsideLeft_free_second
    outsideRight_free_first outsideRight_free_second outsideLeft_ne_outsideRight
    adj_left_p0 adj_right_p2 adj_left_q0 adj_right_q2 rfl

/-- All four bundled branch witnesses are realised by the same graph, so each of
the four `closeLeft`-shaped closures is non-vacuous. -/
theorem allWitnesses :
    SameWindowAttachmentWitness windowObject ∧
      CrossWindowWedgeWitness windowObject ∧
      InterlacedWindowPairWitness windowObject ∧
      TwoWindowPairWitness windowObject := by
  refine ⟨⟨firstWindow, outsideLeft, 0, 6, firstWindow_packed, by omega,
      by omega, outsideLeft_free_first, adj_left_p0, adj_left_p6,
      Or.inr rfl⟩, ?_, ?_, ?_⟩
  · exact ⟨firstWindow, centre, outsideLeft, outsideRight, 6, 2,
      firstWindow_packed, by omega, by omega, centre_free_first,
      outsideLeft_free_first, outsideRight_free_first,
      outsideLeft_ne_outsideRight, adj_centre_left, adj_centre_right,
      adj_left_p6, adj_right_p2, Or.inr (Or.inl rfl)⟩
  · exact ⟨firstWindow, outsideLeft, outsideRight, 0, 2, 6, 8,
      firstWindow_packed, by omega, by omega, by omega, by omega,
      outsideLeft_free_first, outsideRight_free_first,
      outsideLeft_ne_outsideRight, adj_left_p0, adj_left_p6, adj_right_p2,
      adj_right_p8, Or.inl rfl⟩
  · exact ⟨firstWindow, secondWindow, outsideLeft, outsideRight, 0, 2, 0, 2,
      firstWindow_packed, secondWindow_packed, windows_disjoint, by omega,
      by omega, by omega, by omega, outsideLeft_free_first,
      outsideLeft_free_second, outsideRight_free_first, outsideRight_free_second,
      outsideLeft_ne_outsideRight, adj_left_p0, adj_right_p2, adj_left_q0,
      adj_right_q2, Or.inr (Or.inl rfl)⟩

/-- The four `closeLeft`-shaped closures fire on the witness with the accepted
dyadic lengths. -/
theorem closures_fire :
    HasCycleWithLength dyadicLength windowObject := by
  obtain ⟨same, _, _, _⟩ := allWitnesses
  exact hasCycleWithLength_of_sameWindowAttachmentWitness accepted same

/-- The closing side of the node-`[72]` removal is inhabited, so the registered
branch closure is not vacuous. -/
theorem directCycleConfiguration_holds :
    DirectCycleConfiguration windowObject :=
  Or.inl allWitnesses.1

/-- The registered node-`[72]` closure fires on the witness. -/
theorem directCycleClosure_fires :
    HasCycleWithLength dyadicLength windowObject :=
  hasCycleWithLength_of_directCycleConfiguration accepted
    directCycleConfiguration_holds

end Witness

end Hypostructure.Graph.TypeBClosure
