import Hypostructure.Graph.BoundaryDemand
import Hypostructure.Graph.FinitePathSelection

/-!
# Canonical receiver routing inside a support

A support whose vertices all sit at or below a registered degree baseline
splits into *full* vertices, whose neighbours are all internal, and *receivers*,
which still have ports leaving the support.  A discharging argument routes each
full vertex to one receiver along a trace that stays full until its last edge,
and then compares the resulting load against the receiver's own port count.

This module owns that geometry and nothing else:

* `IsReceiver`, `missingPorts` — who receives, and how many ports it has left;
* `TraceTo`, `IsTracePath` — the trace relation a routing follows, as a
  relation and as a predicate on a path;
* `traceReceiver?` — *the* routing, selected by the object's own vertex
  schedule, so no application supplies a route and no route is an arbitrary
  function;
* `tracePath?` — the trace itself, selected by the object's own path schedule,
  for the steps that compare a trace against another path rather than only
  reading its endpoint;
* `routedLoad`, `Saturated` — the load counted at a receiver and the comparison
  a discharging step branches on;
* `exists_traceTo_of_no_baseline_subsupport` — the routing is total whenever no
  subregion of the support meets the baseline, which is what makes the load a
  complete assignment rather than a partial one.

Every threshold is a parameter.  Nothing here knows a degree, an overload
factor, or a graph family, and no declaration mentions a particular argument.
-/

namespace Hypostructure.Graph

universe u

namespace FiniteObject

/-- **A receiver of a support.**  Its internal degree is below the baseline, so
`missingPorts` of its ambient incidences leave the support. -/
def IsReceiver (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat) (vertex : object.Vertex) : Prop :=
  vertex ∈ support ∧ object.internalDegree support vertex < threshold

/-- **`q(w)`.**  The ports a receiver still has leaving the support: the
baseline less what it spends inside.  On a support whose vertices sit exactly at
the baseline this is the number of ambient edges from the vertex to the
complement. -/
noncomputable def missingPorts (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (vertex : object.Vertex) : Nat :=
  threshold - object.internalDegree support vertex

/-- **A full vertex of a support**: it spends the whole baseline internally, so
it has no port of its own and must be routed to a receiver. -/
def IsFullDegree (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat) (vertex : object.Vertex) : Prop :=
  vertex ∈ support ∧ object.internalDegree support vertex = threshold

/-- **Connectivity through full vertices.**  A walk inside the support all of
whose vertices are full.  It is written on ambient walks rather than on the
induced full-degree object so that no restriction has to be built and no walk
has to be transported. -/
def FullConnected (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat) (source target : object.Vertex) : Prop :=
  ∃ walk : object.graph.Walk source target,
    ∀ vertex ∈ walk.support,
      vertex ∈ support ∧ object.internalDegree support vertex = threshold

/-- **The trace relation.**  A path inside the support that stays full until its
last edge and ends at a receiver.  This is the shape a routed trace has; which
one of them is *the* trace is decided by `traceReceiver?` below. -/
def TraceTo (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat) (source target : object.Vertex) : Prop :=
  ∃ walk : object.graph.Walk source target,
    walk.IsPath ∧
      (∀ vertex ∈ walk.support, vertex ∈ support) ∧
      (∀ vertex ∈ walk.support, vertex ≠ target →
        object.internalDegree support vertex = threshold) ∧
      object.internalDegree support target < threshold

theorem mem_support_of_traceTo (object : FiniteObject.{u})
    {support : Finset object.Vertex} {threshold : Nat}
    {source target : object.Vertex}
    (trace : object.TraceTo support threshold source target) :
    source ∈ support ∧ target ∈ support := by
  obtain ⟨walk, _isPath, inside, _full, _receiver⟩ := trace
  exact ⟨inside source walk.start_mem_support,
    inside target walk.end_mem_support⟩

theorem isReceiver_of_traceTo (object : FiniteObject.{u})
    {support : Finset object.Vertex} {threshold : Nat}
    {source target : object.Vertex}
    (trace : object.TraceTo support threshold source target) :
    object.IsReceiver support threshold target :=
  ⟨(object.mem_support_of_traceTo trace).2, trace.choose_spec.2.2.2⟩

/-- **The canonical routing.**  The object's own vertex schedule is scanned once
and the first receiver the source traces to is returned.  Nothing outside this
declaration chooses a route, and the result is an `Option`: a source that traces
to no receiver is *not* silently routed somewhere. -/
noncomputable def traceReceiver? (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (source : object.Vertex) : Option object.Vertex :=
  object.orderedVertices.find? fun candidate =>
    @decide (object.TraceTo support threshold source candidate)
      (Classical.propDecidable _)

/-- A routed source really traces to the receiver it was routed to. -/
theorem traceTo_of_traceReceiver?_eq_some (object : FiniteObject.{u})
    {support : Finset object.Vertex} {threshold : Nat}
    {source target : object.Vertex}
    (routed : object.traceReceiver? support threshold source = some target) :
    object.TraceTo support threshold source target :=
  @of_decide_eq_true _ (Classical.propDecidable _)
    (List.find?_some (p := fun candidate =>
      @decide (object.TraceTo support threshold source candidate)
        (Classical.propDecidable _)) routed)

/-- A source with any trace at all is routed. -/
theorem isSome_traceReceiver?_of_traceTo (object : FiniteObject.{u})
    {support : Finset object.Vertex} {threshold : Nat}
    {source target : object.Vertex}
    (trace : object.TraceTo support threshold source target) :
    (object.traceReceiver? support threshold source).isSome := by
  rcases missing : object.traceReceiver? support threshold source with _ | found
  · exact absurd (@decide_eq_true _ (Classical.propDecidable _) trace)
      (List.find?_eq_none.mp missing target
        (object.mem_orderedVertices target))
  · simp

/-! ## The trace itself

`traceReceiver?` answers *where* a full vertex is routed.  A discharging step
that compares a trace against another path in the support needs the trace, not
only its endpoint, so the same relation is resolved a second time — over the
object's own finite path schedule instead of its vertex schedule.  The two
selections agree by construction: `tracePath?` is asked exactly at the receiver
`traceReceiver?` returns, so there is one routing, not two. -/

/-- The shape of a trace, as a predicate on a path: it stays inside the
support, every vertex but the last is full, and the last is a receiver. -/
def IsTracePath (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat) {source target : object.Vertex}
    (path : object.graph.Walk source target) : Prop :=
  (∀ vertex ∈ path.support, vertex ∈ support) ∧
    (∀ vertex ∈ path.support, vertex ≠ target →
      object.internalDegree support vertex = threshold) ∧
    object.internalDegree support target < threshold

theorem traceTo_iff_exists_isTracePath (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (source target : object.Vertex) :
    object.TraceTo support threshold source target ↔
      ∃ path : object.graph.Path source target,
        object.IsTracePath support threshold path.1 := by
  constructor
  · rintro ⟨walk, isPath, inside, full, receiver⟩
    exact ⟨⟨walk, isPath⟩, inside, full, receiver⟩
  · rintro ⟨path, inside, full, receiver⟩
    exact ⟨path.1, path.2, inside, full, receiver⟩

/-- **`T_u`, the canonical trace.**  The first path of the object's own finite
path schedule from the source to the given receiver that has the trace shape.
The schedule is `Graph.FinitePathSelection.pathSchedule`, the framework's fixed
order — shortest first, then Mathlib's own enumeration — so no application
chooses a trace and no trace is an arbitrary witness. -/
noncomputable def tracePath? (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (source target : object.Vertex) :
    Option (object.graph.Path source target) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := FinEnum.instFintype
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact (FinitePathSelection.pathSchedule object.graph source target).find?
    fun path =>
      @decide (object.IsTracePath support threshold path.1)
        (Classical.propDecidable _)

/-- The canonical trace has the trace shape. -/
theorem isTracePath_of_tracePath?_eq_some (object : FiniteObject.{u})
    {support : Finset object.Vertex} {threshold : Nat}
    {source target : object.Vertex} {path : object.graph.Path source target}
    (selected : object.tracePath? support threshold source target = some path) :
    object.IsTracePath support threshold path.1 := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := FinEnum.instFintype
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact @of_decide_eq_true _ (Classical.propDecidable _)
    (List.find?_some (p := fun candidate =>
      @decide (object.IsTracePath support threshold
          (candidate : object.graph.Path source target).1)
        (Classical.propDecidable _)) selected)

/-- **A routed source has a canonical trace**, and it is a trace to the very
receiver the routing returned.  This is what makes `T_u` and `r(u)` one
routing. -/
theorem isSome_tracePath?_of_traceTo (object : FiniteObject.{u})
    {support : Finset object.Vertex} {threshold : Nat}
    {source target : object.Vertex}
    (trace : object.TraceTo support threshold source target) :
    (object.tracePath? support threshold source target).isSome := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := FinEnum.instFintype
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  obtain ⟨path, shape⟩ :=
    (object.traceTo_iff_exists_isTracePath support threshold source target).mp
      trace
  rcases missing : object.tracePath? support threshold source target with
    _ | found
  · refine absurd (@decide_eq_true _ (Classical.propDecidable _) shape) ?_
    exact List.find?_eq_none.mp missing path
      (FinitePathSelection.mem_pathSchedule object.graph path)
  · simp

/-- **`L(w)`.**  The number of full vertices the canonical routing sends to a
receiver. -/
noncomputable def routedLoad (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver : object.Vertex) : Nat := by
  classical
  exact (support.filter fun source =>
    object.internalDegree support source = threshold ∧
      object.traceReceiver? support threshold source = some receiver).card

/-- **A saturated receiver.**  Its routed load has reached the registered
multiple of its own port count. -/
def Saturated (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold scale : Nat) (receiver : object.Vertex) : Prop :=
  scale * object.missingPorts support threshold receiver ≤
    object.routedLoad support threshold receiver

/-! ## The routing is total

The empty-core hypothesis below is the only thing this needs: no subregion of
the support meets the baseline.  Under it a full vertex cannot be cut off from
the receivers, because the region it reaches through full vertices would
otherwise retain the whole baseline internally. -/

/-- **Every full vertex of the support traces to a receiver.**

Suppose not.  The vertices reachable from the source through full vertices then
have all of their internal neighbours full and again reachable — a neighbour of
lower internal degree would be a receiver, and the walk extended by that edge,
shortened to a path, would be a trace.  So that region spends the whole baseline
inside itself, and it is a subregion of the support meeting the baseline, which
the hypothesis denies. -/
theorem exists_traceTo_of_no_baseline_subsupport (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (capped : ∀ vertex ∈ support,
      object.internalDegree support vertex ≤ threshold)
    (noCore : ∀ inner : Finset object.Vertex, inner ⊆ support →
      ¬ MinimumDegreeAtLeast threshold (object.induce inner))
    {source : object.Vertex} (member : source ∈ support)
    (full : object.internalDegree support source = threshold) :
    ∃ target, object.TraceTo support threshold source target := by
  classical
  by_contra missing
  push Not at missing
  -- The region the source reaches through full vertices.
  set core : Finset object.Vertex :=
    support.filter fun vertex =>
      object.internalDegree support vertex = threshold ∧
        object.FullConnected support threshold source vertex with coreDef
  have coreSubset : core ⊆ support := Finset.filter_subset _ _
  have sourceMem : source ∈ core := by
    refine Finset.mem_filter.mpr ⟨member, full, ?_⟩
    exact ⟨SimpleGraph.Walk.nil, by
      intro vertex inside
      rw [show vertex = source by simpa using inside]
      exact ⟨member, full⟩⟩
  -- An internal neighbour of a reached vertex is again reached.
  have step : ∀ vertex ∈ core, ∀ other : object.Vertex,
      object.graph.Adj vertex other → other ∈ support → other ∈ core := by
    intro vertex vertexMem other adjacent otherMem
    obtain ⟨_vertexInside, _vertexFull, walk, walkFull⟩ :=
      Finset.mem_filter.mp vertexMem
    have extendedSupport :
        (walk.concat adjacent).support = walk.support ++ [other] :=
      SimpleGraph.Walk.support_concat walk adjacent
    have split : ∀ inner ∈ (walk.concat adjacent).support,
        inner ∈ walk.support ∨ inner = other := by
      intro inner inside
      rw [extendedSupport] at inside
      simpa using inside
    -- The neighbour is full: a receiver there would be a trace the source has
    -- been assumed not to have.
    have otherFull : object.internalDegree support other = threshold := by
      rcases Nat.lt_or_ge (object.internalDegree support other) threshold with
        below | above
      · exact absurd
          ⟨(walk.concat adjacent).toPath.1,
            (walk.concat adjacent).toPath.2,
            (by
              intro inner inside
              rcases split inner
                (SimpleGraph.Walk.support_bypass_subset_support _ inside) with
                previous | equal
              · exact (walkFull inner previous).1
              · exact equal ▸ otherMem),
            (by
              intro inner inside distinct
              rcases split inner
                (SimpleGraph.Walk.support_bypass_subset_support _ inside) with
                previous | equal
              · exact (walkFull inner previous).2
              · exact absurd equal distinct),
            below⟩
          (missing other)
      · exact Nat.le_antisymm (capped other otherMem) above
    refine Finset.mem_filter.mpr ⟨otherMem, otherFull, walk.concat adjacent, ?_⟩
    intro inner inside
    rcases split inner inside with previous | equal
    · exact walkFull inner previous
    · exact equal ▸ ⟨otherMem, otherFull⟩
  -- The region keeps the whole baseline inside itself.
  have degreeBound : ∀ vertex ∈ core,
      threshold ≤ object.internalDegree core vertex := by
    intro vertex vertexMem
    obtain ⟨vertexInside, vertexFull, _reached⟩ := Finset.mem_filter.mp vertexMem
    letI : FinEnum object.Vertex := object.vertices
    letI : DecidableRel object.graph.Adj := object.decideAdj
    have contained :
        (object.graph.neighborFinset vertex) ∩ support ⊆
          (object.graph.neighborFinset vertex) ∩ core := by
      intro other inside
      obtain ⟨adjacent, otherMem⟩ := Finset.mem_inter.mp inside
      exact Finset.mem_inter.mpr
        ⟨adjacent, step vertex vertexMem other
          ((SimpleGraph.mem_neighborFinset _ _ _).mp adjacent) otherMem⟩
    have monotone : object.internalDegree support vertex ≤
        object.internalDegree core vertex := by
      simpa [internalDegree] using Finset.card_le_card contained
    exact vertexFull ▸ monotone
  -- A subregion of the support meeting the baseline: excluded by hypothesis.
  refine noCore core coreSubset ?_
  letI : Nonempty (object.induce core).Vertex := ⟨⟨source, sourceMem⟩⟩
  refine (object.induce core).le_minDegree_of_forall_le_degree threshold ?_
  intro vertex
  rw [object.degree_induce_eq_internalDegree core vertex]
  exact degreeBound vertex.1 vertex.2

/-! ## The threshold algebra

A receiver's charge is its port count less one discharge unit, and each routed
load costs one more.  Multiplying through by the scale leaves an exact integer
comparison, which is what `Saturated` is and what its negation gives. -/

/-- **The saturation threshold, indexed by how far the receiver is below the
baseline.**  A receiver of internal degree `threshold − 1 − j` has
`q(w) = j + 1`, so its threshold is `scale·(j + 1)`. -/
theorem saturationThreshold_eq (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    {receiver : object.Vertex}
    (below : object.internalDegree support receiver < threshold) :
    scale * object.missingPorts support threshold receiver =
      scale * (threshold - 1 - object.internalDegree support receiver + 1) := by
  unfold missingPorts
  congr 1
  omega

/-- **The raw ceiling.**  A receiver's threshold never exceeds the scale times
the baseline, because it never has more missing ports than the baseline. -/
theorem saturationThreshold_le (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) :
    scale * object.missingPorts support threshold receiver ≤ scale * threshold :=
  Nat.mul_le_mul_left _ (Nat.sub_le _ _)

/-- **Nonnegative final charge is exactly unsaturation.**  Multiplying
`q(w) − 1/scale − L(w)/scale ≥ 0` by the scale gives `1 + L(w) ≤ scale·q(w)`,
and the first load value that leaves it is `L(w) = scale·q(w)`. -/
theorem not_saturated_iff (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) :
    ¬ object.Saturated support threshold scale receiver ↔
      1 + object.routedLoad support threshold receiver ≤
        scale * object.missingPorts support threshold receiver := by
  unfold Saturated
  omega

end FiniteObject

end Hypostructure.Graph
