import Hypostructure.Graph.ExitFourFamily

/-!
# A compiled inhabitant of the exit-(4) peeling witness

`Graph.ExitFour.Witness` is the type whose *negation* is committed at twelve
statement sites of `Graph/Strategy/SpineVocabulary.lean` (the `¬ ∃ witness : …` arms
of the tested exit-`(4)` dichotomy), and which `route8TrueResidual` and
`route8TrueTwoCarrierEntry` consume.  A negative arm carries information only
if the type it negates is inhabitable: an empty witness type would make every
such arm free, and nothing in the development would fail to compile.

This fixture removes that risk by exhibiting a concrete inhabitant.  The
fixture object is the graph on `Fin 10` with edges

```
0-2 0-6 1-2 1-4 1-5 2-3 3-4 3-5 4-7 5-8 6-7 6-8 7-8
```

and the isolated vertex `9`.  At baseline `3` and discharge scale `4`:

* `0` is the unique receiver of `support = {0,…,8}` (internal degree `2`),
  with `q(0) = 1` completion ports missing and no completion port inside the
  object, so no routed load is visible;
* every one of `1,…,8` is a full vertex routed to `0`, so `L(0) = 8 ≥ 4·q(0)`
  and the receiver is saturated;
* the canonical payable prefix is `{1,2,3}` and the residual excess is
  `E₄(0) = {4,5,6,7,8}`, which is silent -- `SilentUnpeeledExcessAt`;
* the graph has exactly one triangle, `{6,7,8}`, and it lies inside the
  excess basin away from its cut boundary, so the basin's literal boundary
  response (all internal incidences forgotten) loses that triangle while the
  basin itself keeps it.  A single outside context therefore distinguishes the
  two readings: `Response.TargetDefect` for `HasCycleWithLength (· = 3)`.

That is exactly the Q2 clause of `def:typeA-exit4-family`, so
`ExitFour.witnessOfExcessTargetDefect` assembles a genuine
`ExitFour.Witness (object := fixture) (HasCycleWithLength LengthOK) support 3 4 0 ∅`.
-/

namespace Hypostructure.Fixtures.ExitFourWitnessInhabited

open Hypostructure
open Hypostructure.Graph

/-! ## The fixture object -/

/-- Edge list of the fixture graph on `Fin 10`. -/
def edgeList : List (Nat × Nat) :=
  [(0,2),(0,6),(1,2),(1,4),(1,5),(2,3),(3,4),(3,5),(4,7),(5,8),(6,7),(6,8),(7,8)]

def adjBool (a b : Fin 10) : Bool :=
  edgeList.any fun p => (a.val == p.1 && b.val == p.2)

/-- The fixture graph. -/
def fixtureGraph : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel fun a b => adjBool a b = true

instance : DecidableRel fixtureGraph.Adj := fun a b =>
  decidable_of_iff _ (SimpleGraph.fromRel_adj _ a b).symm

/-- The fixture object. -/
abbrev fixture : FiniteObject.{0} where
  Vertex := Fin 10
  graph := fixtureGraph
  vertices := inferInstance
  decideAdj := inferInstance

/-- The selected support: every vertex but the isolated `9`. -/
def support : Finset (Fin 10) := {0,1,2,3,4,5,6,7,8}

/-- The baseline `δ`. -/
def baseline : Nat := 3

/-- The registered discharge scale `s` (the manuscript's four). -/
def dischargeScale : Nat := 4

/-- The accepted cycle lengths. -/
def LengthOK : Nat → Prop := fun length => length = 3

theorem orderedVertices_eq :
    fixture.orderedVertices = [0,1,2,3,4,5,6,7,8,9] := by decide

/-! ## Degrees -/

theorem internalDegree_eq (vertex : Fin 10) (neighbours : Finset (Fin 10))
    (value : Nat)
    (mem : ∀ other : Fin 10, other ∈ neighbours ↔
      (fixtureGraph.Adj vertex other ∧ other ∈ support))
    (card : neighbours.card = value) :
    fixture.internalDegree support vertex = value := by
  classical
  rw [← card]
  simp only [FiniteObject.internalDegree]
  congr 1
  ext other
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, mem]

theorem degree_zero : fixture.internalDegree support 0 = 2 :=
  internalDegree_eq 0 {2,6} 2 (by decide) (by decide)

theorem degree_one : fixture.internalDegree support 1 = 3 :=
  internalDegree_eq 1 {2,4,5} 3 (by decide) (by decide)

theorem degree_two : fixture.internalDegree support 2 = 3 :=
  internalDegree_eq 2 {0,1,3} 3 (by decide) (by decide)

theorem degree_three : fixture.internalDegree support 3 = 3 :=
  internalDegree_eq 3 {2,4,5} 3 (by decide) (by decide)

theorem degree_four : fixture.internalDegree support 4 = 3 :=
  internalDegree_eq 4 {1,3,7} 3 (by decide) (by decide)

theorem degree_five : fixture.internalDegree support 5 = 3 :=
  internalDegree_eq 5 {1,3,8} 3 (by decide) (by decide)

theorem degree_six : fixture.internalDegree support 6 = 3 :=
  internalDegree_eq 6 {0,7,8} 3 (by decide) (by decide)

theorem degree_seven : fixture.internalDegree support 7 = 3 :=
  internalDegree_eq 7 {4,6,8} 3 (by decide) (by decide)

theorem degree_eight : fixture.internalDegree support 8 = 3 :=
  internalDegree_eq 8 {5,6,7} 3 (by decide) (by decide)

theorem degree_nine : fixture.internalDegree support 9 = 0 :=
  internalDegree_eq 9 ∅ 0 (by decide) (by decide)

/-- Every vertex of the support other than the receiver spends the whole
baseline inside it. -/
theorem degree_of_ne (vertex : Fin 10) (ne_zero : vertex ≠ 0)
    (ne_nine : vertex ≠ 9) :
    fixture.internalDegree support vertex = 3 := by
  fin_cases vertex
  · exact absurd rfl ne_zero
  · exact degree_one
  · exact degree_two
  · exact degree_three
  · exact degree_four
  · exact degree_five
  · exact degree_six
  · exact degree_seven
  · exact degree_eight
  · exact absurd rfl ne_nine

/-! ## The canonical routing -/

/-- A walk to `0` inside the support and away from the isolated vertex is a
trace of `def:typeA-exit4-peeling`. -/
theorem traceTo_of_walk (vertex : Fin 10) (walk : fixture.graph.Walk vertex 0)
    (isPath : walk.IsPath)
    (inside : ∀ other ∈ walk.support, other ∈ support ∧ other ≠ 9) :
    fixture.TraceTo support baseline vertex 0 := by
  refine ⟨walk, isPath, fun other member => (inside other member).1, ?_, ?_⟩
  · intro other member ne_zero
    rw [degree_of_ne other ne_zero (inside other member).2]
    decide
  · rw [degree_zero]
    decide

/-- The routing sends every trace to the receiver `0`: it is the first vertex
of the object's own schedule. -/
theorem traceReceiver_eq (vertex : Fin 10)
    (trace : fixture.TraceTo support baseline vertex 0) :
    fixture.traceReceiver? support baseline vertex = some 0 := by
  unfold FiniteObject.traceReceiver?
  rw [orderedVertices_eq]
  exact List.find?_cons_of_pos (@decide_eq_true _ (Classical.propDecidable _) trace)

theorem trace_one : fixture.TraceTo support baseline 1 0 := by
  refine traceTo_of_walk 1 (.cons (show fixture.graph.Adj 1 2 by decide) (.cons (show fixture.graph.Adj 2 0 by decide) .nil)) ?_ ?_
  · simp [SimpleGraph.Walk.isPath_def]
  · decide

theorem trace_two : fixture.TraceTo support baseline 2 0 := by
  refine traceTo_of_walk 2 (.cons (show fixture.graph.Adj 2 0 by decide) .nil) ?_ ?_
  · simp [SimpleGraph.Walk.isPath_def]
  · decide

theorem trace_three : fixture.TraceTo support baseline 3 0 := by
  refine traceTo_of_walk 3 (.cons (show fixture.graph.Adj 3 2 by decide) (.cons (show fixture.graph.Adj 2 0 by decide) .nil)) ?_ ?_
  · simp [SimpleGraph.Walk.isPath_def]
  · decide

theorem trace_four : fixture.TraceTo support baseline 4 0 := by
  refine traceTo_of_walk 4 (.cons (show fixture.graph.Adj 4 1 by decide) (.cons (show fixture.graph.Adj 1 2 by decide) (.cons (show fixture.graph.Adj 2 0 by decide) .nil))) ?_ ?_
  · simp [SimpleGraph.Walk.isPath_def]
  · decide

theorem trace_five : fixture.TraceTo support baseline 5 0 := by
  refine traceTo_of_walk 5 (.cons (show fixture.graph.Adj 5 1 by decide) (.cons (show fixture.graph.Adj 1 2 by decide) (.cons (show fixture.graph.Adj 2 0 by decide) .nil))) ?_ ?_
  · simp [SimpleGraph.Walk.isPath_def]
  · decide

theorem trace_six : fixture.TraceTo support baseline 6 0 := by
  refine traceTo_of_walk 6 (.cons (show fixture.graph.Adj 6 0 by decide) .nil) ?_ ?_
  · simp [SimpleGraph.Walk.isPath_def]
  · decide

theorem trace_seven : fixture.TraceTo support baseline 7 0 := by
  refine traceTo_of_walk 7 (.cons (show fixture.graph.Adj 7 6 by decide) (.cons (show fixture.graph.Adj 6 0 by decide) .nil)) ?_ ?_
  · simp [SimpleGraph.Walk.isPath_def]
  · decide

theorem trace_eight : fixture.TraceTo support baseline 8 0 := by
  refine traceTo_of_walk 8 (.cons (show fixture.graph.Adj 8 6 by decide) (.cons (show fixture.graph.Adj 6 0 by decide) .nil)) ?_ ?_
  · simp [SimpleGraph.Walk.isPath_def]
  · decide

/-- `ℒ(0) = {1,…,8}`. -/
theorem routedLoads_eq :
    fixture.routedLoads support baseline 0 = {1,2,3,4,5,6,7,8} := by
  ext vertex
  rw [FiniteObject.mem_routedLoads]
  constructor
  · rintro ⟨member, full, -⟩
    by_cases zero : vertex = 0
    · subst zero
      rw [degree_zero] at full
      exact absurd full (by decide)
    · clear full
      revert vertex
      decide
  · intro member
    have split : vertex = 1 ∨ vertex = 2 ∨ vertex = 3 ∨ vertex = 4 ∨ vertex = 5 ∨
        vertex = 6 ∨ vertex = 7 ∨ vertex = 8 := by
      revert vertex; decide
    rcases split with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨by decide, degree_one, traceReceiver_eq 1 trace_one⟩,
      ⟨by decide, degree_two, traceReceiver_eq 2 trace_two⟩,
      ⟨by decide, degree_three, traceReceiver_eq 3 trace_three⟩,
      ⟨by decide, degree_four, traceReceiver_eq 4 trace_four⟩,
      ⟨by decide, degree_five, traceReceiver_eq 5 trace_five⟩,
      ⟨by decide, degree_six, traceReceiver_eq 6 trace_six⟩,
      ⟨by decide, degree_seven, traceReceiver_eq 7 trace_seven⟩,
      ⟨by decide, degree_eight, traceReceiver_eq 8 trace_eight⟩]

theorem unpeeledLoads_eq :
    ExitFour.unpeeledLoads (object := fixture) support baseline 0 ∅ =
      {1,2,3,4,5,6,7,8} := by
  rw [ExitFour.unpeeledLoads, routedLoads_eq]
  decide

theorem missingPorts_eq : fixture.missingPorts support baseline 0 = 1 := by
  rw [FiniteObject.missingPorts, degree_zero]
  decide

/-! ## No completion port, hence no visible load -/

theorem completionPorts_eq :
    VisibleEntry.completionPorts fixture support 0 = ∅ := by
  ext vertex
  simp only [Finset.notMem_empty, iff_false]
  intro member
  rw [VisibleEntry.mem_completionPorts] at member
  revert member
  revert vertex
  decide

theorem visibleLoads_eq :
    VisibleEntry.visibleLoads fixture support baseline 0 = ∅ := by
  ext vertex
  simp only [Finset.notMem_empty, iff_false]
  intro member
  rw [VisibleEntry.mem_visibleLoads] at member
  obtain ⟨-, port, portMember, -⟩ := member
  rw [completionPorts_eq] at portMember
  exact absurd portMember (Finset.notMem_empty _)

/-! ## The canonical payable prefix and the residual excess -/

theorem visibleFirstOrder_eq :
    ExitFour.unpeeledVisibleFirstOrder (object := fixture) support baseline 0 ∅ =
      [1,2,3,4,5,6,7,8] := by
  have empty : ∀ vertex : Fin 10,
      (decide (vertex ∈ ExitFour.unpeeledVisibleLoads (object := fixture)
        support baseline 0 ∅)) = false := by
    intro vertex
    refine decide_eq_false ?_
    rw [ExitFour.unpeeledVisibleLoads, visibleLoads_eq]
    simp
  have residual : ∀ vertex : Fin 10,
      (decide (vertex ∈ ExitFour.unpeeledLoads (object := fixture) support baseline 0 ∅ ∧
        vertex ∉ VisibleEntry.visibleLoads fixture support baseline 0)) =
      decide (vertex ∈ ({1,2,3,4,5,6,7,8} : Finset (Fin 10))) := by
    intro vertex
    refine decide_eq_decide.mpr ?_
    rw [unpeeledLoads_eq, visibleLoads_eq]
    simp
  rw [ExitFour.unpeeledVisibleFirstOrder, orderedVertices_eq,
    List.filter_congr (fun vertex _ => empty vertex),
    List.filter_congr (fun vertex _ => residual vertex)]
  decide

theorem payableSet_eq :
    ExitFour.unpeeledPayableSet (object := fixture) support baseline
      dischargeScale 0 ∅ = {1,2,3} := by
  rw [ExitFour.unpeeledPayableSet, visibleFirstOrder_eq, missingPorts_eq]
  decide

theorem excess_eq :
    ExitFour.unpeeledExcess (object := fixture) support baseline
      dischargeScale 0 ∅ = {4,5,6,7,8} := by
  rw [ExitFour.unpeeledExcess, unpeeledLoads_eq, payableSet_eq]
  decide

/-- The receiver is saturated at the registered scale: `4·q(0) = 4 ≤ 8 = L(0)`. -/
theorem saturated :
    fixture.Saturated support baseline dischargeScale 0 := by
  rw [FiniteObject.Saturated, FiniteObject.routedLoad, routedLoads_eq,
    missingPorts_eq]
  decide

/-- The residual excess is silent: there is no completion port at all, the
excess is nonempty, and no excess load is visible. -/
theorem silent :
    ExitFour.SilentUnpeeledExcessAt (object := fixture) support baseline
      dischargeScale 0 ∅ := by
  refine ⟨?_, ?_, ?_⟩
  · intro port member
    rw [completionPorts_eq] at member
    exact absurd member (Finset.notMem_empty _)
  · rw [excess_eq]; exact ⟨4, by decide⟩
  · rw [excess_eq, unpeeledLoads_eq, visibleLoads_eq]
    decide

theorem excess_member :
    (4 : Fin 10) ∈ ExitFour.unpeeledExcess (object := fixture) support baseline
      dischargeScale 0 ∅ := by
  rw [excess_eq]; decide

/-! ## The excess basin `B(0)` -/

open Hypostructure.Graph.Strategy.InterfaceReplacement in
noncomputable abbrev basin : Finset (Fin 10) :=
  ExitFour.excessTraceSupport fixture support baseline dischargeScale 0 ∅

theorem zero_mem_basin : (0 : Fin 10) ∈ basin := by
  unfold basin ExitFour.excessTraceSupport
  exact Finset.mem_insert_self _ _

theorem mem_basin_of_excess {vertex : Fin 10}
    (member : vertex ∈ ExitFour.unpeeledExcess (object := fixture) support
      baseline dischargeScale 0 ∅) :
    vertex ∈ basin := by
  unfold basin ExitFour.excessTraceSupport
  exact Finset.mem_insert_of_mem (Finset.mem_union_left _ member)

theorem mem_basin_of_seed {load vertex : Fin 10}
    (loadMember : load ∈ ExitFour.unpeeledExcess (object := fixture) support
      baseline dischargeScale 0 ∅)
    (member : vertex ∈
      (Route8.TraceBasin.traceSeed? fixture support baseline 0 load).getD ∅) :
    vertex ∈ basin := by
  unfold basin ExitFour.excessTraceSupport
  exact Finset.mem_insert_of_mem (Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨load, loadMember, member⟩))

theorem mem_basin_of_closure (vertex : Fin 10)
    (member : vertex ∈ ({0,4,5,6,7,8} : Finset (Fin 10))) : vertex ∈ basin := by
  by_cases zero : vertex = 0
  · subst zero; exact zero_mem_basin
  · refine mem_basin_of_excess ?_
    rw [excess_eq]
    have shrink : ∀ other : Fin 10, ¬ other = 0 →
        other ∈ ({0,4,5,6,7,8} : Finset (Fin 10)) →
        other ∈ ({4,5,6,7,8} : Finset (Fin 10)) := by decide
    exact shrink vertex zero member

theorem seed_subset (load : Fin 10) :
    ((Route8.TraceBasin.traceSeed? fixture support baseline 0 load).getD ∅) ⊆
      support := by
  unfold Route8.TraceBasin.traceSeed?
  split
  · simp
  · rename_i trace selected
    intro vertex member
    exact (FiniteObject.isTracePath_of_tracePath?_eq_some fixture selected).1 vertex
      (List.mem_toFinset.mp member)

theorem basin_subset : basin ⊆ support := by
  intro vertex member
  unfold basin ExitFour.excessTraceSupport at member
  rcases Finset.mem_insert.mp member with rfl | member
  · decide
  rcases Finset.mem_union.mp member with member | member
  · rw [excess_eq] at member
    have inside : ({4,5,6,7,8} : Finset (Fin 10)) ⊆ support := by decide
    exact inside member
  · obtain ⟨load, -, member⟩ := Finset.mem_biUnion.mp member
    exact seed_subset load member

theorem basin_proper : ∃ vertex : Fin 10, vertex ∉ basin :=
  ⟨9, fun member => absurd (basin_subset member) (by decide)⟩

/-! ## The basin is connected -/

theorem exists_tracePath (load : Fin 10)
    (member : load ∈ ({4,5,6,7,8} : Finset (Fin 10))) :
    ∃ trace : fixture.graph.Path load 0,
      fixture.tracePath? support baseline load 0 = some trace := by
  refine Option.isSome_iff_exists.mp ?_
  have split : load = 4 ∨ load = 5 ∨ load = 6 ∨ load = 7 ∨ load = 8 := by
    revert load; decide
  rcases split with rfl | rfl | rfl | rfl | rfl
  exacts [FiniteObject.isSome_tracePath?_of_traceTo fixture trace_four,
    FiniteObject.isSome_tracePath?_of_traceTo fixture trace_five,
    FiniteObject.isSome_tracePath?_of_traceTo fixture trace_six,
    FiniteObject.isSome_tracePath?_of_traceTo fixture trace_seven,
    FiniteObject.isSome_tracePath?_of_traceTo fixture trace_eight]

theorem seed_eq {load : Fin 10} {trace : fixture.graph.Path load 0}
    (selected : fixture.tracePath? support baseline load 0 = some trace) :
    (Route8.TraceBasin.traceSeed? fixture support baseline 0 load).getD ∅ =
      trace.1.support.toFinset := by
  simp [Route8.TraceBasin.traceSeed?, selected]

theorem walk_to_receiver (vertex : Fin 10) (member : vertex ∈ basin) :
    ∃ walk : fixture.graph.Walk vertex 0, ∀ other ∈ walk.support, other ∈ basin := by
  unfold basin ExitFour.excessTraceSupport at member
  rcases Finset.mem_insert.mp member with rfl | member
  · exact ⟨.nil, by simpa using zero_mem_basin⟩
  have excessMember : ∀ {load : Fin 10},
      load ∈ ExitFour.unpeeledExcess (object := fixture) support baseline
        dischargeScale 0 ∅ → load ∈ ({4,5,6,7,8} : Finset (Fin 10)) := by
    intro load member
    rwa [excess_eq] at member
  rcases Finset.mem_union.mp member with member | member
  · obtain ⟨trace, selected⟩ := exists_tracePath vertex (excessMember member)
    refine ⟨trace.1, fun other inWalk => ?_⟩
    exact mem_basin_of_seed member (by rw [seed_eq selected]; exact List.mem_toFinset.mpr inWalk)
  · obtain ⟨load, loadMember, member⟩ := Finset.mem_biUnion.mp member
    obtain ⟨trace, selected⟩ := exists_tracePath load (excessMember loadMember)
    rw [seed_eq selected] at member
    refine ⟨trace.1.dropUntil vertex (List.mem_toFinset.mp member), fun other inWalk => ?_⟩
    refine mem_basin_of_seed loadMember ?_
    rw [seed_eq selected]
    exact List.mem_toFinset.mpr
      (SimpleGraph.Walk.support_dropUntil_subset_support _ _ inWalk)

theorem basin_connected :
    SupportComponents.Connected.ConnectedOn fixture basin := by
  refine ⟨⟨0, zero_mem_basin⟩, ?_⟩
  intro left right leftMember rightMember
  obtain ⟨leftWalk, leftInside⟩ := walk_to_receiver left leftMember
  obtain ⟨rightWalk, rightInside⟩ := walk_to_receiver right rightMember
  refine ⟨(leftWalk.append rightWalk.reverse).bypass,
    SimpleGraph.Walk.bypass_isPath _, fun vertex member => ?_⟩
  have inWalk := SimpleGraph.Walk.support_bypass_subset_support _ member
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp inWalk with inLeft | inRight
  · exact leftInside vertex inLeft
  · exact rightInside vertex (by simpa using inRight)

/-! ## The two readings of the basin and one outside context -/

open Hypostructure.Graph.Strategy.InterfaceReplacement in
noncomputable abbrev bdry : Boundary.{0} := SupportAtom.boundary fixture basin

noncomputable abbrev leftPiece : BoundaryPiece bdry :=
  ExitFour.excessBoundaryResponse fixture support baseline dischargeScale 0 ∅

open Hypostructure.Graph.Strategy.InterfaceReplacement in
noncomputable abbrev rightPiece : BoundaryPiece bdry :=
  SupportAtom.piece fixture basin

/-- The outside context that distinguishes the two readings: the empty one. -/
noncomputable def emptyOutside : OutsideContext bdry where
  Internal := Fin 0
  internalVertices := inferInstance
  graph := ⊥
  decideAdj := Classical.decRel _

open Hypostructure.Graph.Strategy.InterfaceReplacement in
/-- Each triangle vertex lies in the basin, away from its cut boundary. -/
theorem triangle_internal (vertex : Fin 10)
    (member : vertex ∈ ({6,7,8} : Finset (Fin 10))) :
    vertex ∈ basin ∧ vertex ∉ SupportAtom.cutBoundary fixture basin := by
  refine ⟨mem_basin_of_closure vertex (by revert member; revert vertex; decide), ?_⟩
  intro cut
  obtain ⟨-, neighbour, adjacent, outside⟩ :=
    (SupportAtom.mem_cutBoundary_iff fixture basin vertex).mp cut
  refine outside (mem_basin_of_closure neighbour ?_)
  have closure : ∀ base ∈ ({6,7,8} : Finset (Fin 10)), ∀ other : Fin 10,
      fixtureGraph.Adj base other → other ∈ ({0,4,5,6,7,8} : Finset (Fin 10)) := by
    decide
  exact closure vertex member neighbour adjacent

/-! ## The basin realizes the triangle; its boundary response does not -/

open Hypostructure.Graph.Strategy.InterfaceReplacement in
noncomputable def rightVertex (vertex : Fin 10)
    (member : vertex ∈ ({6,7,8} : Finset (Fin 10))) :
    GluedVertex rightPiece emptyOutside :=
  Sum.inr (Sum.inl ⟨vertex, triangle_internal vertex member⟩)

noncomputable def rightAmbient : GluedVertex rightPiece emptyOutside → Fin 10
  | .inl boundaryVertex => boundaryVertex.1
  | .inr (.inl internal) => internal.1
  | .inr (.inr nothing) => nothing.elim0

theorem rightVertex_inj {a b : Fin 10} {ha hb} (equal : rightVertex a ha = rightVertex b hb) :
    a = b := congrArg rightAmbient equal

theorem rightVertex_ne {a b : Fin 10} {ha hb} (distinct : ¬ a = b) :
    ¬ rightVertex a ha = rightVertex b hb :=
  fun equal => distinct (rightVertex_inj equal)

theorem right_adj {a b : Fin 10} (ha : a ∈ ({6,7,8} : Finset (Fin 10)))
    (hb : b ∈ ({6,7,8} : Finset (Fin 10))) (adjacent : fixtureGraph.Adj a b) :
    (glue rightPiece emptyOutside).graph.Adj (rightVertex a ha) (rightVertex b hb) :=
  (glueGraph_adj_iff rightPiece emptyOutside _ _).mpr
    (Or.inl ⟨Sum.inr ⟨a, triangle_internal a ha⟩, Sum.inr ⟨b, triangle_internal b hb⟩,
      adjacent, rfl, rfl⟩)

noncomputable def triangleWalk :
    (glue rightPiece emptyOutside).graph.Walk
      (rightVertex 6 (by decide)) (rightVertex 6 (by decide)) :=
  .cons (right_adj (b := 7) (by decide) (by decide) (by decide))
    (.cons (right_adj (a := 7) (b := 8) (by decide) (by decide) (by decide))
      (.cons (right_adj (a := 8) (b := 6) (by decide) (by decide) (by decide)) .nil))

theorem triangleWalk_isCycle : triangleWalk.IsCycle := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [triangleWalk]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;>
      first
        | exact rightVertex_ne (by decide)
        | exact fun _ => rightVertex_ne (by decide)
  · simp [triangleWalk]
  · simp [triangleWalk]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> exact rightVertex_ne (by decide)

theorem right_has_cycle :
    HasCycleWithLength LengthOK (glue rightPiece emptyOutside) :=
  ⟨{ vertex := rightVertex 6 (by decide)
     walk := triangleWalk
     isCycle := triangleWalk_isCycle
     length_ok := by show triangleWalk.length = 3; rfl }⟩

/-! ## The literal boundary response has no accepted cycle -/

noncomputable def ambient : GluedVertex leftPiece emptyOutside → Fin 10
  | .inl boundaryVertex => boundaryVertex.1
  | .inr (.inl internal) => internal.1
  | .inr (.inr nothing) => nothing.elim0

open Hypostructure.Graph.Strategy.InterfaceReplacement in
theorem ambient_pieceEmbedding (piecewise : bdry.Vertex ⊕ leftPiece.Internal) :
    ambient (pieceEmbedding leftPiece emptyOutside piecewise) =
      SupportAtom.pieceDecode fixture basin piecewise := by
  cases piecewise <;> rfl

open Hypostructure.Graph.Strategy.InterfaceReplacement in
theorem decode_mem_cutBoundary (piecewise : bdry.Vertex ⊕ leftPiece.Internal)
    (left : piecewise.isLeft = true) :
    SupportAtom.pieceDecode fixture basin piecewise ∈
      SupportAtom.cutBoundary fixture basin := by
  revert left
  cases piecewise with
  | inl boundaryVertex => exact fun _ => boundaryVertex.2
  | inr internal => exact fun left => by simp at left

open Hypostructure.Graph.Strategy.InterfaceReplacement in
/-- Every edge of the glued boundary response is an ambient edge with an
endpoint on the cut boundary: the internal incidences have been forgotten. -/
theorem left_edge {x y : GluedVertex leftPiece emptyOutside}
    (adjacent : (glue leftPiece emptyOutside).graph.Adj x y) :
    fixtureGraph.Adj (ambient x) (ambient y) ∧
      (ambient x ∈ SupportAtom.cutBoundary fixture basin ∨
        ambient y ∈ SupportAtom.cutBoundary fixture basin) := by
  rcases (glueGraph_adj_iff leftPiece emptyOutside x y).mp adjacent with
    ⟨s, t, owned, hs, ht⟩ | ⟨s, t, owned, -, -⟩
  · subst hs
    subst ht
    rw [ambient_pieceEmbedding, ambient_pieceEmbedding]
    refine ⟨owned.1, ?_⟩
    rcases owned.2.2 with side | side
    · rcases side with left | left | ⟨empty, -⟩
      · exact Or.inl (decode_mem_cutBoundary s left)
      · exact Or.inr (decode_mem_cutBoundary t left)
      · exact absurd empty (Finset.notMem_empty _)
    · rcases side with left | left | ⟨empty, -⟩
      · exact Or.inr (decode_mem_cutBoundary t left)
      · exact Or.inl (decode_mem_cutBoundary s left)
      · exact absurd empty (Finset.notMem_empty _)
  · exact absurd owned (by simp [emptyOutside])

theorem unique_triangle : ∀ p q r : Fin 10, fixtureGraph.Adj p q →
    fixtureGraph.Adj q r → fixtureGraph.Adj r p →
    p ∈ ({6,7,8} : Finset (Fin 10)) ∧ q ∈ ({6,7,8} : Finset (Fin 10)) := by
  decide

theorem left_no_cycle :
    ¬ HasCycleWithLength LengthOK (glue leftPiece emptyOutside) := by
  rintro ⟨⟨start, walk, isCycle, lengthOK⟩⟩
  have length : walk.length = 3 := lengthOK
  clear isCycle
  cases walk with
  | nil => simp at length
  | cons first rest =>
    cases rest with
    | nil => simp at length
    | cons second rest =>
      cases rest with
      | nil => simp at length
      | cons third rest =>
        cases rest with
        | cons fourth rest => simp at length
        | nil =>
          obtain ⟨adj1, cut⟩ := left_edge first
          obtain ⟨adj2, -⟩ := left_edge second
          obtain ⟨adj3, -⟩ := left_edge third
          obtain ⟨member1, member2⟩ := unique_triangle _ _ _ adj1 adj2 adj3
          rcases cut with cut | cut
          · exact (triangle_internal _ member1).2 cut
          · exact (triangle_internal _ member2).2 cut

/-! ## The exit-(4) witness -/

open Hypostructure.Graph.Strategy.InterfaceReplacement in
theorem targetDefect :
    Response.TargetDefect (HasCycleWithLength LengthOK)
      (ExitFour.excessBoundaryResponse fixture support baseline dischargeScale 0 ∅)
      (SupportAtom.piece fixture
        (ExitFour.excessTraceSupport fixture support baseline dischargeScale 0 ∅)) :=
  ⟨emptyOutside, fun equivalent => left_no_cycle (equivalent.mpr right_has_cycle)⟩

/-- **The compiled exit-(4) peeling witness.**  `def:typeA-exit4-peeling`: the
quotient is the Q2 member of `def:typeA-exit4-family`, the two realizations are
the basin's literal boundary response and the basin itself, and `emptyOutside`
is the compatible outside context distinguishing their target predicates. -/
noncomputable def witness :
    ExitFour.Witness (object := fixture) (HasCycleWithLength LengthOK) support baseline
      dischargeScale 0 ∅ :=
  ExitFour.witnessOfExcessTargetDefect silent excess_member basin_subset
    basin_connected basin_proper targetDefect

/-- **The exit-(4) witness type is inhabited.** -/
theorem witness_inhabited :
    Nonempty (ExitFour.Witness (object := fixture) (HasCycleWithLength LengthOK) support baseline
      dischargeScale 0 ∅) :=
  ⟨witness⟩

theorem witness_load : witness.load = 4 := rfl

theorem witness_clause : witness.member.clause = ExitFour.ReceiverClause.silentBasin := rfl

theorem witness_routed :
    witness.load ∈ fixture.routedLoads support baseline 0 :=
  witness.routed

/-- The negative arm of the tested exit-`(4)` dichotomy is **refutable**: it is
false on this object, at this receiver, for this peeling set.  A committed
`¬ ∃ witness …` is therefore a real restriction, not a free statement. -/
theorem negative_arm_is_not_free :
    ¬ (¬ ∃ found : ExitFour.Witness (object := fixture) (HasCycleWithLength LengthOK) support
        baseline dischargeScale 0 ∅,
      found.load ∈ ExitFour.unpeeledExcess (object := fixture) support baseline
        dischargeScale 0 ∅) :=
  fun negative => negative ⟨witness, excess_member⟩

/-- The same statement in the shape committed at nodes `[113]`/`[114]`. -/
theorem negative_arm_is_not_free_at_load :
    ¬ (¬ ∃ found : ExitFour.Witness (object := fixture) (HasCycleWithLength LengthOK) support
        baseline dischargeScale 0 ∅, found.load = 4) :=
  fun negative => negative ⟨witness, witness_load⟩

end Hypostructure.Fixtures.ExitFourWitnessInhabited
