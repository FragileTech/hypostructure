import Hypostructure.Graph.WindowPacking
import Hypostructure.Graph.Target

/-!
# Direct fan-window and two-window cycles

This is the mathematics of the *structural* half of manuscript node `[72]`:
`lem:typeB-direct-fan-window-cycles` and `lem:typeB-two-window-cycles`.  Both
say the same thing in four displays: a fan centre whose closed neighbours attach
to packed windows at the wrong coordinates closes an accepted cycle, so the
configuration cannot survive on a branch whose object avoids those lengths.

Nothing here mentions a manuscript, a numeral, or a fixed target.  The accepted
lengths are the parameter `LengthOK`, the window order is the parameter `order`,
and the arithmetic side conditions of `def:direct-cycle-free-closed-pair` are
*stated as* `LengthOK` of the length the corresponding cycle has.  At the
manuscript's power-of-two target and its window order those readings are
literally its `b − a ∈ {2, 6}`, `|x − y| ∈ {0, 4, 12}`, `L_× ∈ {8, 16}` and
`|i − j| + |a − b| ∈ {0, 4, 12}`: inside a window of order `13` the only accepted
values of `(b − a) + 2` are `4` and `8`, the only accepted values of
`4 + |x − y|` are `4`, `8` and `16`, and likewise for the other two.  Writing
each condition as the length of its own cycle keeps the set out of the source,
where it would be a constant the framework has no business knowing.

## What is assumed

Nothing of the form "configuration `X` does not occur".  A window enters
positively, through `IsWindowPacking`: the packing supplies each window's
induced path embedding, from which `Presentation` reads the coordinate map, the
displayed edges, and the distinctness of the coordinates.  The manuscript's two
standing side conditions are, respectively, a positive statement about the
supplied outside vertices (`u, v ∉ W`) and a *theorem* rather than a hypothesis
(the packed windows are vertex-disjoint -- the packing's own clause).
-/

namespace Hypostructure.Graph.TypeBDirectCycle

open Hypostructure

universe u

variable {object : FiniteObject.{u}} {order : Nat} {LengthOK : Nat → Prop}

/-! ## The two cycle shapes

Every cycle built below is one of the two shapes drawn in the proof of
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

/-- The attachment cycle, packaged as a cycle certificate. -/
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

/-- The cross cycle, packaged as a cycle certificate. -/
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

/-! ## A packed window, read by its coordinates

`IsWindowPacking` gives each window an induced path embedding.  A
`Presentation` is that embedding read as the manuscript's `P = p₀p₁⋯`: the
coordinate map, the displayed edges, and the distinctness of the coordinates.
Inducedness is never used below -- only the displayed edges and the
distinctness -- so it is not recorded. -/

/-- The manuscript's packed window `P = p₀p₁⋯p_{order−1}`, presented in the
ambient graph by its coordinate map together with the support it occupies. -/
structure Presentation (object : FiniteObject.{u}) (order : Nat) where
  /-- `p_i`.  Only the coordinates `i < order` are ever used. -/
  coordinate : Nat → object.Vertex
  /-- The window support the coordinates occupy. -/
  support : Finset object.Vertex
  /-- `p_i p_{i+1} ∈ E(G)`. -/
  step : ∀ i, i + 1 < order →
    object.graph.Adj (coordinate i) (coordinate (i + 1))
  /-- The displayed vertices are pairwise distinct. -/
  distinct : ∀ i < order, ∀ j < order, coordinate i = coordinate j → i = j
  /-- The coordinates land in the support. -/
  covers : ∀ i < order, coordinate i ∈ support

namespace Presentation

/-- **Every window of a packing has a presentation.**

The window's induced path embedding, composed with the canonical inclusion of
the induced restriction, is the coordinate map; `pathGraph_adj` supplies the
displayed edges and the embedding's injectivity the distinctness.  Nothing is
assumed: the embedding is the packing's own `InducesWindow` clause. -/
theorem exists_of_inducesWindow (object : FiniteObject.{u}) {order : Nat}
    (positive : 0 < order) {support : Finset object.Vertex}
    (window : object.InducesWindow order support) :
    ∃ presentation : Presentation object order, presentation.support = support := by
  classical
  obtain ⟨⟨embedding⟩, _cardinality⟩ := window
  refine ⟨⟨fun index =>
      if bound : index < order then (embedding ⟨index, bound⟩).1
      else (embedding ⟨0, positive⟩).1,
    support, ?_, ?_, ?_⟩, rfl⟩
  · -- `step`: the displayed edges, from `pathGraph_adj` through both embeddings.
    intro index bound
    have first : index < order := by omega
    have adjacency :
        (SimpleGraph.pathGraph order).Adj ⟨index, first⟩ ⟨index + 1, bound⟩ :=
      SimpleGraph.pathGraph_adj.2 (Or.inl rfl)
    have inside := embedding.map_adj_iff.2 adjacency
    have ambient := (object.induceEmbedding support).map_adj_iff.2 inside
    simpa [first, bound] using ambient
  · -- `distinct`: the embedding is injective.
    intro index boundIndex other boundOther equal
    rw [dif_pos boundIndex, dif_pos boundOther] at equal
    exact congrArg Fin.val (embedding.injective (Subtype.ext equal))
  · -- `covers`: an embedded coordinate is a vertex of the induced restriction.
    intro index bound
    simp only [dif_pos bound]
    exact (embedding ⟨index, bound⟩).2

/-- The forward stretch `p_i P p_{i+n}` of a presented window. -/
private theorem exists_forwardSegment (presentation : Presentation object order)
    (i : Nat) :
    ∀ n, i + n < order →
      ∃ segment : object.graph.Walk (presentation.coordinate i)
          (presentation.coordinate (i + n)),
        segment.IsPath ∧ segment.length = n ∧
          ∀ z ∈ segment.support,
            ∃ t, t ≤ n ∧ z = presentation.coordinate (i + t) := by
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
          object.graph.Adj (presentation.coordinate (i + n))
            (presentation.coordinate (i + n + 1)) :=
        presentation.step (i + n) (by omega)
      have fresh : presentation.coordinate (i + n + 1) ∉ segment.support := by
        intro inside
        obtain ⟨t, small, equal⟩ := member _ inside
        have index :=
          presentation.distinct (i + n + 1) (by omega) (i + t) (by omega) equal
        omega
      have supportEq :
          (segment.append
            (SimpleGraph.Walk.cons adjacency SimpleGraph.Walk.nil)).support
            = segment.support ++ [presentation.coordinate (i + n + 1)] := by
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

/-- **The window stretch `p_i P p_j`**: a path of length `|i − j|` all of whose
vertices are window coordinates between `i` and `j`.

Both readings are needed downstream: the length is the cycle length, and the
location of the support gives the disjointness of two stretches and the
avoidance by the outside vertices. -/
theorem exists_stretch (presentation : Presentation object order) {i j : Nat}
    (sourceBound : i < order) (targetBound : j < order) :
    ∃ segment : object.graph.Walk (presentation.coordinate i)
        (presentation.coordinate j),
      segment.IsPath ∧ segment.length = max i j - min i j ∧
        ∀ z ∈ segment.support,
          ∃ t, min i j ≤ t ∧ t ≤ max i j ∧ z = presentation.coordinate t := by
  rcases Nat.le_total i j with ordering | ordering
  · obtain ⟨n, rfl⟩ : ∃ n, j = i + n := ⟨j - i, by omega⟩
    obtain ⟨segment, path, length, member⟩ :=
      exists_forwardSegment presentation i n targetBound
    refine ⟨segment, path, by omega, ?_⟩
    intro z inside
    obtain ⟨t, small, equal⟩ := member _ inside
    exact ⟨i + t, by omega, by omega, equal⟩
  · obtain ⟨n, rfl⟩ : ∃ n, i = j + n := ⟨i - j, by omega⟩
    obtain ⟨segment, path, length, member⟩ :=
      exists_forwardSegment presentation j n sourceBound
    refine ⟨segment.reverse, path.reverse, ?_, ?_⟩
    · rw [SimpleGraph.Walk.length_reverse, length]
      omega
    · intro z inside
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at inside
      obtain ⟨t, small, equal⟩ := member _ inside
      exact ⟨j + t, by omega, by omega, equal⟩

/-- A vertex outside the window coordinates misses every window stretch. -/
theorem not_mem_support_of_outside {presentation : Presentation object order}
    {i j : Nat}
    {segment : object.graph.Walk (presentation.coordinate i)
      (presentation.coordinate j)}
    (member : ∀ z ∈ segment.support,
      ∃ t, min i j ≤ t ∧ t ≤ max i j ∧ z = presentation.coordinate t)
    (sourceBound : i < order) (targetBound : j < order)
    {vertex : object.Vertex}
    (outside : ∀ t < order, vertex ≠ presentation.coordinate t) :
    vertex ∉ segment.support := by
  intro inside
  obtain ⟨t, lower, upper, equal⟩ := member _ inside
  exact outside t (by omega) equal

/-- **Two stretches of one window in disjoint index ranges are
vertex-disjoint.**  The coordinates are distinct, so a shared vertex would
force a shared index. -/
theorem stretches_disjoint {presentation : Presentation object order}
    {firstLow firstHigh secondLow secondHigh : Nat}
    {first : object.graph.Walk (presentation.coordinate firstLow)
      (presentation.coordinate firstHigh)}
    {second : object.graph.Walk (presentation.coordinate secondLow)
      (presentation.coordinate secondHigh)}
    (firstMember : ∀ z ∈ first.support,
      ∃ t, min firstLow firstHigh ≤ t ∧ t ≤ max firstLow firstHigh ∧
        z = presentation.coordinate t)
    (secondMember : ∀ z ∈ second.support,
      ∃ t, min secondLow secondHigh ≤ t ∧ t ≤ max secondLow secondHigh ∧
        z = presentation.coordinate t)
    (firstBound : max firstLow firstHigh < order)
    (secondBound : max secondLow secondHigh < order)
    (separated : max firstLow firstHigh < min secondLow secondHigh) :
    ∀ ⦃z : object.Vertex⦄, z ∈ first.support → z ∉ second.support := by
  intro z inFirst inSecond
  obtain ⟨s, sLow, sHigh, sEq⟩ := firstMember _ inFirst
  obtain ⟨t, tLow, tHigh, tEq⟩ := secondMember _ inSecond
  have indices :=
    presentation.distinct s (by omega) t (by omega) (sEq ▸ tEq ▸ rfl)
  omega

/-- **A stretch of one window misses a stretch of a disjoint window.** -/
theorem stretches_disjoint_of_disjoint_support
    {presentation other : Presentation object order}
    {firstLow firstHigh secondLow secondHigh : Nat}
    {first : object.graph.Walk (presentation.coordinate firstLow)
      (presentation.coordinate firstHigh)}
    {second : object.graph.Walk (other.coordinate secondLow)
      (other.coordinate secondHigh)}
    (firstMember : ∀ z ∈ first.support,
      ∃ t, min firstLow firstHigh ≤ t ∧ t ≤ max firstLow firstHigh ∧
        z = presentation.coordinate t)
    (secondMember : ∀ z ∈ second.support,
      ∃ t, min secondLow secondHigh ≤ t ∧ t ≤ max secondLow secondHigh ∧
        z = other.coordinate t)
    (firstBound : max firstLow firstHigh < order)
    (secondBound : max secondLow secondHigh < order)
    (disjoint : Disjoint presentation.support other.support) :
    ∀ ⦃z : object.Vertex⦄, z ∈ first.support → z ∉ second.support := by
  intro z inFirst inSecond
  obtain ⟨s, _sLow, sHigh, sEq⟩ := firstMember _ inFirst
  obtain ⟨t, _tLow, tHigh, tEq⟩ := secondMember _ inSecond
  exact (Finset.disjoint_left.mp disjoint (sEq ▸ presentation.covers s (by omega)))
    (tEq ▸ other.covers t (by omega))

end Presentation

/-! ## The four direct configurations

Each is the manuscript's display, with the arithmetic side condition read as
"the length of the cycle this display builds is accepted".  Each is stated at a
given fan centre and over the windows of a given packing; the Type B scoping of
the centre -- assigned to a connected negative-charge support, high-degree,
certificate-marked -- is the caller's, exactly as for every other fact of this
branch. -/

/-- **`lem:typeB-direct-fan-window-cycles` (a).**  A closed neighbour of the
centre attaches to one window at two coordinates whose stretch closes an
accepted cycle. -/
def SameWindowAttachment (object : FiniteObject.{u}) (order : Nat)
    (LengthOK : Nat → Prop) (packing : Finset (Finset object.Vertex))
    (centre : object.Vertex) : Prop :=
  ∃ presentation : Presentation object order, presentation.support ∈ packing ∧
    ∃ owner : object.Vertex, object.graph.Adj centre owner ∧
      (∀ t < order, owner ≠ presentation.coordinate t) ∧
      ∃ low high : Nat, low < high ∧ high < order ∧
        object.graph.Adj owner (presentation.coordinate low) ∧
        object.graph.Adj owner (presentation.coordinate high) ∧
        LengthOK (high - low + 2)

/-- **`lem:typeB-direct-fan-window-cycles` (b).**  Two distinct closed
neighbours of the centre attach to one window at coordinates whose stretch
closes the wedge `u — h — v` into an accepted cycle. -/
def CrossWindowWedge (object : FiniteObject.{u}) (order : Nat)
    (LengthOK : Nat → Prop) (packing : Finset (Finset object.Vertex))
    (centre : object.Vertex) : Prop :=
  ∃ presentation : Presentation object order, presentation.support ∈ packing ∧
    ∃ left right : object.Vertex, left ≠ right ∧
      centre ≠ left ∧ centre ≠ right ∧
      object.graph.Adj left centre ∧ object.graph.Adj centre right ∧
      (∀ t < order, centre ≠ presentation.coordinate t) ∧
      (∀ t < order, left ≠ presentation.coordinate t) ∧
      (∀ t < order, right ≠ presentation.coordinate t) ∧
      ∃ leftIndex rightIndex : Nat, leftIndex < order ∧ rightIndex < order ∧
        object.graph.Adj (presentation.coordinate leftIndex) left ∧
        object.graph.Adj right (presentation.coordinate rightIndex) ∧
        LengthOK (4 + (max leftIndex rightIndex - min leftIndex rightIndex))

/-- **`lem:typeB-direct-fan-window-cycles` (c).**  Two distinct closed
neighbours of the centre whose closed labels interlace, `a_u < a_v < b_u < b_v`,
close the interlacing cycle of length `L_×(u,v)`. -/
def InterlacedWindowPair (object : FiniteObject.{u}) (order : Nat)
    (LengthOK : Nat → Prop) (packing : Finset (Finset object.Vertex))
    (centre : object.Vertex) : Prop :=
  ∃ presentation : Presentation object order, presentation.support ∈ packing ∧
    ∃ left right : object.Vertex, left ≠ right ∧
      object.graph.Adj centre left ∧ object.graph.Adj centre right ∧
      (∀ t < order, left ≠ presentation.coordinate t) ∧
      (∀ t < order, right ≠ presentation.coordinate t) ∧
      ∃ leftLow rightLow leftHigh rightHigh : Nat,
        leftLow < rightLow ∧ rightLow < leftHigh ∧ leftHigh < rightHigh ∧
        rightHigh < order ∧
        object.graph.Adj left (presentation.coordinate leftLow) ∧
        object.graph.Adj left (presentation.coordinate leftHigh) ∧
        object.graph.Adj right (presentation.coordinate rightLow) ∧
        object.graph.Adj right (presentation.coordinate rightHigh) ∧
        LengthOK (4 + (rightLow - leftLow) + (rightHigh - leftHigh))

/-- **`lem:typeB-two-window-cycles`.**  Two distinct closed neighbours of the
centre with incidences to two *distinct* packed windows close the two-window
cycle of length `4 + |i − j| + |a − b|`. -/
def TwoWindowPair (object : FiniteObject.{u}) (order : Nat)
    (LengthOK : Nat → Prop) (packing : Finset (Finset object.Vertex))
    (centre : object.Vertex) : Prop :=
  ∃ first second : Presentation object order,
    first.support ∈ packing ∧ second.support ∈ packing ∧
      first.support ≠ second.support ∧
      ∃ left right : object.Vertex, left ≠ right ∧
        object.graph.Adj centre left ∧ object.graph.Adj centre right ∧
        (∀ t < order, left ≠ first.coordinate t) ∧
        (∀ t < order, left ≠ second.coordinate t) ∧
        (∀ t < order, right ≠ first.coordinate t) ∧
        (∀ t < order, right ≠ second.coordinate t) ∧
        ∃ leftFirst rightFirst leftSecond rightSecond : Nat,
          leftFirst < order ∧ rightFirst < order ∧
          leftSecond < order ∧ rightSecond < order ∧
          object.graph.Adj left (first.coordinate leftFirst) ∧
          object.graph.Adj right (first.coordinate rightFirst) ∧
          object.graph.Adj left (second.coordinate leftSecond) ∧
          object.graph.Adj right (second.coordinate rightSecond) ∧
          LengthOK (4 + (max leftFirst rightFirst - min leftFirst rightFirst) +
            (max leftSecond rightSecond - min leftSecond rightSecond))

/-- **`def:direct-cycle-free-closed-pair`, negated.**  The centre carries one of
the four direct configurations. -/
def DirectCycleConfiguration (object : FiniteObject.{u}) (order : Nat)
    (LengthOK : Nat → Prop) (packing : Finset (Finset object.Vertex))
    (centre : object.Vertex) : Prop :=
  SameWindowAttachment object order LengthOK packing centre ∨
    CrossWindowWedge object order LengthOK packing centre ∨
      InterlacedWindowPair object order LengthOK packing centre ∨
        TwoWindowPair object order LengthOK packing centre

/-- **`def:direct-cycle-free-closed-pair`.**  Every closed fan-window pair at
the centre is direct-cycle-free. -/
def DirectCycleFree (object : FiniteObject.{u}) (order : Nat)
    (LengthOK : Nat → Prop) (packing : Finset (Finset object.Vertex))
    (centre : object.Vertex) : Prop :=
  ¬ DirectCycleConfiguration object order LengthOK packing centre

/-! ## The four eliminations -/

/-- **`lem:typeB-direct-fan-window-cycles`, first display.** -/
theorem hasCycleWithLength_of_sameWindowAttachment
    {packing : Finset (Finset object.Vertex)} {centre : object.Vertex}
    (configuration : SameWindowAttachment object order LengthOK packing centre) :
    HasCycleWithLength LengthOK object := by
  obtain ⟨presentation, _member, owner, _hub, windowFree, low, high, increasing,
    bound, lower, upper, accepted⟩ := configuration
  obtain ⟨segment, path, length, member⟩ :=
    Presentation.exists_stretch presentation (i := low) (j := high) (by omega) bound
  have avoids : owner ∉ segment.support :=
    Presentation.not_mem_support_of_outside member (by omega) bound windowFree
  have endsNe :
      presentation.coordinate low ≠ presentation.coordinate high := by
    intro equal
    exact absurd (presentation.distinct low (by omega) high bound equal) (by omega)
  refine ⟨attachmentCertificate lower upper.symm path endsNe avoids ?_⟩
  rw [length]
  have rewrite : max low high - min low high = high - low := by omega
  rw [rewrite]
  exact accepted

/-- **`lem:typeB-direct-fan-window-cycles`, second display.** -/
theorem hasCycleWithLength_of_crossWindowWedge
    {packing : Finset (Finset object.Vertex)} {centre : object.Vertex}
    (configuration : CrossWindowWedge object order LengthOK packing centre) :
    HasCycleWithLength LengthOK object := by
  obtain ⟨presentation, _member, left, right, distinct, centreNeLeft,
    centreNeRight, leftHub, rightHub, centreFree, leftFree, rightFree,
    leftIndex, rightIndex, leftBound, rightBound, leftAttachment,
    rightAttachment, accepted⟩ := configuration
  obtain ⟨segment, path, length, member⟩ :=
    Presentation.exists_stretch presentation (i := rightIndex) (j := leftIndex)
      rightBound leftBound
  have leftAvoids : left ∉ segment.support :=
    Presentation.not_mem_support_of_outside member rightBound leftBound leftFree
  have rightAvoids : right ∉ segment.support :=
    Presentation.not_mem_support_of_outside member rightBound leftBound rightFree
  have centreAvoids : centre ∉ segment.support :=
    Presentation.not_mem_support_of_outside member rightBound leftBound centreFree
  refine ⟨crossCertificate (firstSegment := SimpleGraph.Walk.nil (u := centre))
    (secondSegment := segment) leftHub rightHub rightAttachment leftAttachment
    SimpleGraph.Walk.IsPath.nil path ?_ distinct ?_ leftAvoids ?_ rightAvoids ?_⟩
  · intro z inFirst
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at inFirst
    exact inFirst ▸ centreAvoids
  · rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
    exact fun same => centreNeLeft same.symm
  · rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
    exact fun same => centreNeRight same.symm
  · rw [SimpleGraph.Walk.length_nil, length, Nat.zero_add]
    have rewrite :
        max rightIndex leftIndex - min rightIndex leftIndex + 4 =
          4 + (max leftIndex rightIndex - min leftIndex rightIndex) := by omega
    rw [rewrite]
    exact accepted

/-- **`lem:typeB-direct-fan-window-cycles`, third display.** -/
theorem hasCycleWithLength_of_interlacedWindowPair
    {packing : Finset (Finset object.Vertex)} {centre : object.Vertex}
    (configuration : InterlacedWindowPair object order LengthOK packing centre) :
    HasCycleWithLength LengthOK object := by
  obtain ⟨presentation, _member, left, right, distinct, _leftHub, _rightHub,
    leftFree, rightFree, leftLow, rightLow, leftHigh, rightHigh, firstOrder,
    secondOrder, thirdOrder, bound, leftLowAdj, leftHighAdj, rightLowAdj,
    rightHighAdj, accepted⟩ := configuration
  obtain ⟨firstSegment, firstPath, firstLength, firstMember⟩ :=
    Presentation.exists_stretch presentation (i := leftLow) (j := rightLow)
      (by omega) (by omega)
  obtain ⟨secondSegment, secondPath, secondLength, secondMember⟩ :=
    Presentation.exists_stretch presentation (i := rightHigh) (j := leftHigh)
      bound (by omega)
  have leftAvoidsFirst : left ∉ firstSegment.support :=
    Presentation.not_mem_support_of_outside firstMember (by omega) (by omega)
      leftFree
  have leftAvoidsSecond : left ∉ secondSegment.support :=
    Presentation.not_mem_support_of_outside secondMember bound (by omega) leftFree
  have rightAvoidsFirst : right ∉ firstSegment.support :=
    Presentation.not_mem_support_of_outside firstMember (by omega) (by omega)
      rightFree
  have rightAvoidsSecond : right ∉ secondSegment.support :=
    Presentation.not_mem_support_of_outside secondMember bound (by omega) rightFree
  have segmentsDisjoint :
      ∀ ⦃z : object.Vertex⦄, z ∈ firstSegment.support →
        z ∉ secondSegment.support :=
    Presentation.stretches_disjoint firstMember secondMember (by omega) (by omega)
      (by omega)
  refine ⟨crossCertificate leftLowAdj rightLowAdj.symm rightHighAdj
    leftHighAdj.symm firstPath secondPath segmentsDisjoint distinct
    leftAvoidsFirst leftAvoidsSecond rightAvoidsFirst rightAvoidsSecond ?_⟩
  rw [firstLength, secondLength]
  have rewrite :
      max leftLow rightLow - min leftLow rightLow +
          (max rightHigh leftHigh - min rightHigh leftHigh) + 4 =
        4 + (rightLow - leftLow) + (rightHigh - leftHigh) := by omega
  rw [rewrite]
  exact accepted

/-- **`lem:typeB-two-window-cycles`.**

The vertex-disjointness of the two windows is the packing's own clause, read at
the two supports the configuration names. -/
theorem hasCycleWithLength_of_twoWindowPair
    {packing : Finset (Finset object.Vertex)} {centre : object.Vertex}
    (valid : object.IsWindowPacking order packing)
    (configuration : TwoWindowPair object order LengthOK packing centre) :
    HasCycleWithLength LengthOK object := by
  obtain ⟨first, second, firstMemberPacking, secondMemberPacking, supportsNe,
    left, right, distinct, _leftHub, _rightHub, leftFreeFirst, leftFreeSecond,
    rightFreeFirst, rightFreeSecond, leftFirst, rightFirst, leftSecond,
    rightSecond, leftFirstBound, rightFirstBound, leftSecondBound,
    rightSecondBound, leftFirstAdj, rightFirstAdj, leftSecondAdj,
    rightSecondAdj, accepted⟩ := configuration
  have disjointSupports : Disjoint first.support second.support :=
    valid.2 _ firstMemberPacking _ secondMemberPacking supportsNe
  obtain ⟨firstSegment, firstPath, firstLength, firstMember⟩ :=
    Presentation.exists_stretch first (i := leftFirst) (j := rightFirst)
      leftFirstBound rightFirstBound
  obtain ⟨secondSegment, secondPath, secondLength, secondMember⟩ :=
    Presentation.exists_stretch second (i := rightSecond) (j := leftSecond)
      rightSecondBound leftSecondBound
  have leftAvoidsFirst : left ∉ firstSegment.support :=
    Presentation.not_mem_support_of_outside firstMember leftFirstBound
      rightFirstBound leftFreeFirst
  have leftAvoidsSecond : left ∉ secondSegment.support :=
    Presentation.not_mem_support_of_outside secondMember rightSecondBound
      leftSecondBound leftFreeSecond
  have rightAvoidsFirst : right ∉ firstSegment.support :=
    Presentation.not_mem_support_of_outside firstMember leftFirstBound
      rightFirstBound rightFreeFirst
  have rightAvoidsSecond : right ∉ secondSegment.support :=
    Presentation.not_mem_support_of_outside secondMember rightSecondBound
      leftSecondBound rightFreeSecond
  have segmentsDisjoint :
      ∀ ⦃z : object.Vertex⦄, z ∈ firstSegment.support →
        z ∉ secondSegment.support :=
    Presentation.stretches_disjoint_of_disjoint_support firstMember secondMember
      (by omega) (by omega) disjointSupports
  refine ⟨crossCertificate leftFirstAdj rightFirstAdj.symm rightSecondAdj
    leftSecondAdj.symm firstPath secondPath segmentsDisjoint distinct
    leftAvoidsFirst leftAvoidsSecond rightAvoidsFirst rightAvoidsSecond ?_⟩
  rw [firstLength, secondLength]
  have rewrite :
      max leftFirst rightFirst - min leftFirst rightFirst +
          (max rightSecond leftSecond - min rightSecond leftSecond) + 4 =
        4 + (max leftFirst rightFirst - min leftFirst rightFirst) +
          (max leftSecond rightSecond - min leftSecond rightSecond) := by omega
  rw [rewrite]
  exact accepted

/-- **`lem:typeB-direct-fan-window-cycles` and `lem:typeB-two-window-cycles`
together.**  A centre carrying any of the four direct configurations hands the
branch an accepted cycle. -/
theorem hasCycleWithLength_of_directCycleConfiguration
    {packing : Finset (Finset object.Vertex)} {centre : object.Vertex}
    (valid : object.IsWindowPacking order packing)
    (configuration :
      DirectCycleConfiguration object order LengthOK packing centre) :
    HasCycleWithLength LengthOK object := by
  rcases configuration with same | wedge | interlaced | twoWindow
  · exact hasCycleWithLength_of_sameWindowAttachment same
  · exact hasCycleWithLength_of_crossWindowWedge wedge
  · exact hasCycleWithLength_of_interlacedWindowPair interlaced
  · exact hasCycleWithLength_of_twoWindowPair valid twoWindow

end Hypostructure.Graph.TypeBDirectCycle
