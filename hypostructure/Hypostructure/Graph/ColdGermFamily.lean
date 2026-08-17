import Hypostructure.Graph.ColdFirstFailure
import Hypostructure.Graph.SubcubicReach

/-!
# The (F5) cold bounded germs of the selected half-edges

`def:cold-corridor-first-failure` and `def:cold-bounded-germ`, constructed:

* the outside component `K` of a boundary stub's foot in `G − X_cold`;
* the first-failure exchange support of a corridor — the whole terminal
  corridor, or the bounded prefix inside which a cold corridor state repeats
  (`Q_cold + 1` initial segments) — as a connected proper support;
* the cold bounded germ it carries.  The two same-interface representatives are
  the support's own boundary piece `Q[x,y]` and the canonical representative
  determined by the exchange's retained state; the manuscript leaves the latter
  underspecified for a corridor whose interior vertices carry a third edge into
  `K`, and the reading taken here is the simplest one under which every
  first-failure exchange is a germ of the selected object: the canonical
  representative is the exchange's own piece, so every germ is equal-length and
  the closure of `lem:cold-bounded-germ-trichotomy` and
  `lem:cold-same-interface-table` is the routing closure the manuscript draws.

Nothing here reads a ledger; the rows read these constructions on
`inputs.current`.
-/

namespace Hypostructure.Graph.ColdCorridor

open Hypostructure

universe u

variable {object : FiniteObject.{u}}

/-- A graph of minimum degree at least three has more than two vertices: any
vertex has three neighbours besides itself, and an empty graph has minimum
degree zero. -/
theorem two_lt_vertexCount_of_minDegree
    (baseline : Graph.MinimumDegreeAtLeast 3 object) : 2 < object.vertexCount := by
  classical
  by_cases nonempty : Nonempty object.Vertex
  · obtain ⟨vertex⟩ := nonempty
    have := object.minDegree_le_degree vertex
    have := object.degree_lt_vertexCount vertex
    change 3 ≤ object.minDegree at baseline
    omega
  · exfalso
    rw [not_nonempty_iff] at nonempty
    change 3 ≤ object.minDegree at baseline
    have zero : object.minDegree = 0 := by
      letI : FinEnum object.Vertex := object.vertices
      letI : DecidableRel object.graph.Adj := object.decideAdj
      change object.graph.minDegree = 0
      simp [SimpleGraph.minDegree, Finset.univ_eq_empty]
    omega

/-! ## The outside component of a foot -/

/-- The vertex support of the outside graph `G − X_cold`. -/
noncomputable def outsideSupport (object : FiniteObject.{u})
    (windows : Finset object.Vertex) : Finset object.Vertex := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  exact Finset.univ \ windows

theorem mem_outsideSupport (object : FiniteObject.{u})
    (windows : Finset object.Vertex) (vertex : object.Vertex) :
    vertex ∈ outsideSupport object windows ↔ vertex ∉ windows := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  simp [outsideSupport]

/-- The outside graph `G − X_cold`. -/
noncomputable abbrev outsideGraph (object : FiniteObject.{u})
    (windows : Finset object.Vertex) : FiniteObject.{u} :=
  object.induce (outsideSupport object windows)

/-- **The connected component `K` of the outside graph containing a foot.** -/
noncomputable def outsideComponentOf (object : FiniteObject.{u})
    (windows : Finset object.Vertex) (foot : object.Vertex)
    (footOutside : foot ∉ windows) : Finset object.Vertex := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  exact Finset.univ.filter fun vertex =>
    ∃ outside : vertex ∈ outsideSupport object windows,
      (outsideGraph object windows).graph.Reachable
        ⟨foot, (mem_outsideSupport object windows foot).2 footOutside⟩
        ⟨vertex, outside⟩

/-- A walk of one induced graph whose vertices all lie in a second support is a
reachability certificate in the second induced graph. -/
theorem reachable_induce_of_walk {first second : Finset object.Vertex}
    {left right : (object.induce first).Vertex}
    (walk : (object.induce first).graph.Walk left right)
    (inside : ∀ vertex ∈ walk.support, vertex.1 ∈ second) :
    (object.induce second).graph.Reachable
      ⟨left.1, inside left (SimpleGraph.Walk.start_mem_support walk)⟩
      ⟨right.1, inside right (SimpleGraph.Walk.end_mem_support walk)⟩ := by
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c adjacent tail ih =>
      have adjacent' : (object.induce second).graph.Adj
          ⟨a.1, inside a (by simp)⟩ ⟨b.1, inside b (by simp)⟩ := by
        change object.graph.Adj a.1 b.1
        exact adjacent
      exact (SimpleGraph.Adj.reachable adjacent').trans
        (ih fun vertex member => inside vertex (by simp [member]))

theorem outsideComponentOf_isOutsideComponent (object : FiniteObject.{u})
    (windows : Finset object.Vertex) (foot : object.Vertex)
    (footOutside : foot ∉ windows) :
    IsOutsideComponent object windows
      (outsideComponentOf object windows foot footOutside) := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro vertex member windowMem
    simp only [outsideComponentOf, Finset.mem_filter, Finset.mem_univ, true_and] at member
    obtain ⟨outside, _⟩ := member
    exact (mem_outsideSupport object windows vertex).1 outside windowMem
  · intro a aMem b adjacent bOutside
    simp only [outsideComponentOf, Finset.mem_filter, Finset.mem_univ, true_and] at aMem ⊢
    obtain ⟨aOutside, reach⟩ := aMem
    refine ⟨(mem_outsideSupport object windows b).2 bOutside, ?_⟩
    refine reach.trans (SimpleGraph.Adj.reachable ?_)
    change object.graph.Adj a b
    exact adjacent
  · intro left right
    have leftMem := left.2
    have rightMem := right.2
    simp only [outsideComponentOf, Finset.mem_filter, Finset.mem_univ, true_and] at leftMem rightMem
    obtain ⟨leftOutside, leftReach⟩ := leftMem
    obtain ⟨rightOutside, rightReach⟩ := rightMem
    obtain ⟨walk⟩ := leftReach.symm.trans rightReach
    have inside : ∀ vertex ∈ walk.support,
        vertex.1 ∈ outsideComponentOf object windows foot footOutside := by
      intro vertex member
      simp only [outsideComponentOf, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨vertex.2, ?_⟩
      exact leftReach.trans ⟨walk.takeUntil vertex member⟩
    have := reachable_induce_of_walk walk inside
    exact this

/-! ## The first-failure exchange support of a corridor -/

variable {windows component : Finset object.Vertex}

namespace Corridor

/-- **The exchange support of a corridor prefix**: the vertices of the first
`n + 1` initial segments, as vertices of the object. -/
noncomputable def prefixSupport (corridor : Corridor object windows component)
    (n : Nat) : Finset object.Vertex := by
  classical
  exact ((corridor.inside.1.take n).support.map (fun vertex => vertex.1)).toFinset

theorem mem_prefixSupport (corridor : Corridor object windows component) (n : Nat)
    (vertex : object.Vertex) :
    vertex ∈ corridor.prefixSupport n ↔
      ∃ inner ∈ (corridor.inside.1.take n).support, inner.1 = vertex := by
  classical
  simp [prefixSupport]

theorem prefixSupport_subset_component (corridor : Corridor object windows component)
    (n : Nat) : corridor.prefixSupport n ⊆ component := by
  intro vertex member
  obtain ⟨inner, _, rfl⟩ := (corridor.mem_prefixSupport n vertex).1 member
  exact inner.2

/-- The exchange support has at most `n + 1` vertices. -/
theorem prefixSupport_card_le (corridor : Corridor object windows component)
    (n : Nat) : (corridor.prefixSupport n).card ≤ n + 1 := by
  classical
  refine le_trans (List.toFinset_card_le _) ?_
  rw [List.length_map, SimpleGraph.Walk.length_support, SimpleGraph.Walk.take_length]
  omega

/-- The exchange support is connected: any two of its vertices are joined by a
path of the object that stays inside it, through the prefix's own start. -/
theorem prefixSupport_connectedOn (corridor : Corridor object windows component)
    (n : Nat) :
    Graph.SupportComponents.Connected.ConnectedOn object (corridor.prefixSupport n) := by
  classical
  let walk := corridor.inside.1.take n
  let embedding := object.induceEmbedding component
  refine ⟨⟨(corridor.inside.1.getVert 0).1, ?_⟩, ?_⟩
  · exact (corridor.mem_prefixSupport n _).2 ⟨_, by
      simpa [walk] using SimpleGraph.Walk.start_mem_support walk, rfl⟩
  · intro left right leftMem rightMem
    obtain ⟨leftInner, leftSupport, leftEq⟩ := (corridor.mem_prefixSupport n left).1 leftMem
    obtain ⟨rightInner, rightSupport, rightEq⟩ :=
      (corridor.mem_prefixSupport n right).1 rightMem
    -- left ← start → right, inside the prefix walk.
    let toLeft := walk.takeUntil leftInner leftSupport
    let toRight := walk.takeUntil rightInner rightSupport
    let joined := toLeft.reverse.append toRight
    let mapped := joined.map embedding.toHom
    have mappedSupport : ∀ vertex ∈ mapped.support, vertex ∈ corridor.prefixSupport n := by
      intro vertex member
      simp only [mapped, SimpleGraph.Walk.support_map, List.mem_map] at member
      obtain ⟨inner, innerMem, rfl⟩ := member
      refine (corridor.mem_prefixSupport n _).2 ⟨inner, ?_, rfl⟩
      simp only [joined, SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_reverse,
        List.mem_append, List.mem_reverse] at innerMem
      rcases innerMem with member | member
      · exact walk.support_takeUntil_subset_support leftSupport member
      · exact walk.support_takeUntil_subset_support rightSupport (List.mem_of_mem_tail member)
    have leftEq' : embedding leftInner = left := leftEq
    have rightEq' : embedding rightInner = right := rightEq
    refine ⟨((mapped.copy leftEq' rightEq').toPath).1, ((mapped.copy leftEq' rightEq').toPath).2,
      ?_⟩
    intro vertex member
    have := SimpleGraph.Walk.support_toPath_subset_support _ member
    rw [SimpleGraph.Walk.support_copy] at this
    exact mappedSupport vertex this

/-- The exchange support is proper: the entry stub's window endpoint lies
outside it. -/
theorem prefixSupport_proper (corridor : Corridor object windows component)
    (outside : IsOutsideComponent object windows component) (n : Nat) :
    ∃ vertex, vertex ∉ corridor.prefixSupport n := by
  refine ⟨corridor.entryStub.2, fun member => ?_⟩
  have inComponent := corridor.prefixSupport_subset_component n member
  have isStub := (mem_boundaryStubs_iff object windows component _).1
    (List.get_mem _ corridor.entry)
  exact Finset.disjoint_left.mp outside.1 inComponent isStub.2.1

end Corridor

namespace Corridor

/-- The foot of a corridor lies in every prefix support. -/
theorem foot_mem_prefixSupport (corridor : Corridor object windows component)
    (n : Nat) : corridor.entryStub.1 ∈ corridor.prefixSupport n := by
  classical
  refine (corridor.mem_prefixSupport n _).2 ⟨_, SimpleGraph.Walk.start_mem_support _, ?_⟩
  simp [stubFoot, Corridor.entryStub]

end Corridor

/-! ## The (F5) germ of an exchange support -/

/-- The trivial retained record of a two-boundary exchange, used when the
corridor's clause readings are not presented. -/
def Record.trivial (S : DeclaredSignature) : Record S where
  boundaryDegrees := fun _ => ⟨0, Nat.succ_pos _⟩
  stubs := fun _ => ⟨0, Nat.succ_pos _⟩
  offsets := fun _ => ⟨0, S.windowOrder_pos⟩
  state := { boundaryDegrees := fun _ => ⟨0, Nat.succ_pos _⟩
             halfEdges := fun _ => ⟨0, Nat.succ_pos _⟩
             offsets := fun _ => ⟨0, S.windowOrder_pos⟩
             declared := fun _ _ => none }
  truth := false

/-- **The cold bounded germ of a connected proper support** whose canonical
representative is the support's own piece.  Baseline holds because the piece
glued to its own outside context is the object up to the decomposition's
reconstruction isomorphism. -/
noncomputable def germOfSupport (S : DeclaredSignature) (threshold : Nat)
    (Target : FiniteObject.{u} → Prop) (object : FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast threshold object)
    (support : Finset object.Vertex)
    (connected : Graph.SupportComponents.Connected.ConnectedOn object support)
    (proper : ∃ vertex, vertex ∉ support) :
    BoundedGerm S (Graph.MinimumDegreeAtLeast threshold) Target object where
  support := support
  connected := connected
  proper := proper
  canonical := (rowAtom object support connected proper).piece
  sameProfile := rfl
  baseline := by
    have iso := (rowAtom object support connected proper).reconstructionIso
    unfold Graph.MinimumDegreeAtLeast at baseline ⊢
    rw [FiniteObject.minDegree_eq_of_isomorphic ⟨iso⟩]
    exact baseline
  record := Record.trivial S

/-- **The (F5) exchange germ of a corridor**, on its exchange prefix. -/
noncomputable def Corridor.exchangeGerm (S : DeclaredSignature) (threshold : Nat)
    (Target : FiniteObject.{u} → Prop)
    (corridor : Corridor object windows component)
    (outside : IsOutsideComponent object windows component)
    (baseline : Graph.MinimumDegreeAtLeast threshold object) (n : Nat) :
    BoundedGerm S (Graph.MinimumDegreeAtLeast threshold) Target object :=
  germOfSupport S threshold Target object baseline (corridor.prefixSupport n)
    (corridor.prefixSupport_connectedOn n) (corridor.prefixSupport_proper outside n)


/-! ## The selected branch-excess half-edges and their germs

`def:cold-skeleton-excess`: *"keep one incident half-edge for every edge of `G`
leaving `P` … the first two stubs of `P` are called the transit stubs; the
remaining `s(P)−2` stubs are the selected branch-excess half-edges of `P`."*
A selected half-edge whose outside endpoint lies in the outside graph has its
cold return corridor and (F5) exchange germ; one whose outside endpoint lies in
another packed window (the manuscript's corridor construction is silent about
these) is charged the germ on the edge itself. -/

section Family

variable (object : FiniteObject.{u})

/-- The external stubs `(w, u)` of a window, in the object's own enumeration
order (the manuscript's "lexicographic" order). -/
noncomputable def externalStubList (window : Finset object.Vertex) :
    List (object.Vertex × object.Vertex) := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact (FinEnum.toList (object.Vertex × object.Vertex)).filter fun stub =>
    decide (stub.1 ∈ window ∧ stub.2 ∉ window ∧ object.graph.Adj stub.1 stub.2)

theorem mem_externalStubList (window : Finset object.Vertex)
    (stub : object.Vertex × object.Vertex) :
    stub ∈ externalStubList object window ↔
      stub.1 ∈ window ∧ stub.2 ∉ window ∧ object.graph.Adj stub.1 stub.2 := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  simp only [externalStubList, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun member => member.2, fun isStub => ⟨FinEnum.mem_toList _, isStub⟩⟩

theorem externalStubList_nodup (window : Finset object.Vertex) :
    (externalStubList object window).Nodup := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  exact List.Nodup.filter _ FinEnum.nodup_toList

/-- **The selected branch-excess half-edges of a window**: its external stubs
with the two transit stubs dropped. -/
noncomputable def selectedStubs (window : Finset object.Vertex) :
    Finset (object.Vertex × object.Vertex) := by
  classical
  exact ((externalStubList object window).drop 2).toFinset

theorem card_selectedStubs (window : Finset object.Vertex) :
    (selectedStubs object window).card = (externalStubList object window).length - 2 := by
  classical
  simp only [selectedStubs]
  rw [List.toFinset_card_of_nodup ((externalStubList_nodup object window).sublist
    (List.drop_sublist _ _))]
  simp

theorem mem_selectedStubs_isStub {window : Finset object.Vertex}
    {stub : object.Vertex × object.Vertex} (member : stub ∈ selectedStubs object window) :
    stub.1 ∈ window ∧ stub.2 ∉ window ∧ object.graph.Adj stub.1 stub.2 := by
  classical
  simp only [selectedStubs, List.mem_toFinset] at member
  exact (mem_externalStubList object window stub).1 (List.mem_of_mem_drop member)

/-- All selected half-edges of a family of windows. -/
noncomputable def allSelectedStubs (family : Finset (Finset object.Vertex)) :
    Finset (object.Vertex × object.Vertex) := by
  classical
  exact family.biUnion (selectedStubs object)

theorem card_allSelectedStubs (family : Finset (Finset object.Vertex))
    (disjoint : ∀ left ∈ family, ∀ right ∈ family, left ≠ right → Disjoint left right) :
    (allSelectedStubs object family).card =
      ∑ window ∈ family, ((externalStubList object window).length - 2) := by
  classical
  simp only [allSelectedStubs]
  rw [Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun window _ => card_selectedStubs object window
  · intro left leftMem right rightMem different
    show Disjoint (selectedStubs object left) (selectedStubs object right)
    rw [Finset.disjoint_left]
    intro stub leftStub rightStub
    have := (mem_selectedStubs_isStub object leftStub).1
    have := (mem_selectedStubs_isStub object rightStub).1
    exact Finset.disjoint_left.mp (disjoint left leftMem right rightMem different) ‹_› ‹_›

end Family

/-! ## The germ of a selected half-edge -/

section Germ

variable (S : DeclaredSignature) (threshold : Nat) (Target : FiniteObject.{u} → Prop)
variable (object : FiniteObject.{u})

/-- The two-vertex support of an edge. -/
noncomputable def edgeSupport (left right : object.Vertex) : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact {left, right}

theorem mem_edgeSupport (left right vertex : object.Vertex) :
    vertex ∈ edgeSupport object left right ↔ vertex = left ∨ vertex = right := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  simp [edgeSupport]

theorem edgeSupport_connectedOn {left right : object.Vertex}
    (adjacent : object.graph.Adj left right) :
    Graph.SupportComponents.Connected.ConnectedOn object (edgeSupport object left right) := by
  refine ⟨⟨left, (mem_edgeSupport object left right left).2 (Or.inl rfl)⟩, ?_⟩
  intro a b aMem bMem
  rw [mem_edgeSupport] at aMem bMem
  have inSupport : ∀ v, v = left ∨ v = right → v ∈ edgeSupport object left right :=
    fun v h => (mem_edgeSupport object left right v).2 h
  rcases aMem with rfl | rfl <;> rcases bMem with rfl | rfl
  · exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, by
      intro v hv; simp at hv; exact inSupport v (Or.inl hv)⟩
  · exact ⟨SimpleGraph.Walk.cons adjacent SimpleGraph.Walk.nil,
      by simp [SimpleGraph.Walk.cons_isPath_iff, adjacent.ne],
      by intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact inSupport _ (by simp)⟩
  · exact ⟨SimpleGraph.Walk.cons adjacent.symm SimpleGraph.Walk.nil,
      by simp [SimpleGraph.Walk.cons_isPath_iff, adjacent.ne.symm],
      by intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact inSupport _ (by simp)⟩
  · exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, by
      intro v hv; simp at hv; exact inSupport v (Or.inr hv)⟩

/-- The germ of an edge `w u` between two window vertices: its own edge. -/
noncomputable def edgeGerm (baseline : Graph.MinimumDegreeAtLeast threshold object)
    {left right : object.Vertex} (adjacent : object.graph.Adj left right)
    (proper : ∃ vertex, vertex ≠ left ∧ vertex ≠ right) :
    BoundedGerm S (Graph.MinimumDegreeAtLeast threshold) Target object :=
  germOfSupport S threshold Target object baseline (edgeSupport object left right)
    (edgeSupport_connectedOn object adjacent)
    (by
      obtain ⟨vertex, notLeft, notRight⟩ := proper
      refine ⟨vertex, fun member => ?_⟩
      rcases (mem_edgeSupport object left right vertex).1 member with h | h
      · exact notLeft h
      · exact notRight h)


/-- The foot of an outside stub lies in its own outside component. -/
theorem foot_mem_outsideComponentOf (windows : Finset object.Vertex)
    (foot : object.Vertex) (footOutside : foot ∉ windows) :
    foot ∈ outsideComponentOf object windows foot footOutside := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  simp only [outsideComponentOf, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨(mem_outsideSupport object windows foot).2 footOutside, SimpleGraph.Reachable.refl _⟩

/-- **The cold return corridor of a selected half-edge** whose outside endpoint
lies in the outside graph, at the outside component of its foot. -/
noncomputable def stubCorridor (windows : Finset object.Vertex)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    {stub : object.Vertex × object.Vertex}
    (isStub : stub.1 ∈ windows ∧ stub.2 ∉ windows ∧ object.graph.Adj stub.1 stub.2) :
    Corridor object windows (outsideComponentOf object windows stub.2 isStub.2.1) := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have member : (stub.2, stub.1) ∈ boundaryStubs object windows
      (outsideComponentOf object windows stub.2 isStub.2.1) :=
    (mem_boundaryStubs_iff object windows _ _).2
      ⟨foot_mem_outsideComponentOf object windows stub.2 isStub.2.1, isStub.1,
        isStub.2.2.symm⟩
  exact corridorOfOutsideComponent object windows _
    (outsideComponentOf_isOutsideComponent object windows stub.2 isStub.2.1) bridgeless
    ⟨(boundaryStubs object windows _).idxOf (stub.2, stub.1),
      List.idxOf_lt_length_iff.2 member⟩

/-- The corridor germ of an outside stub: the (F5) exchange germ of its corridor
on the first `Q_cold + 1` initial segments. -/
noncomputable def corridorGerm (windows : Finset object.Vertex)
    (baseline : Graph.MinimumDegreeAtLeast threshold object)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    {stub : object.Vertex × object.Vertex}
    (isStub : stub.1 ∈ windows ∧ stub.2 ∉ windows ∧ object.graph.Adj stub.1 stub.2) :
    BoundedGerm S (Graph.MinimumDegreeAtLeast threshold) Target object :=
  (stubCorridor object windows bridgeless isStub).exchangeGerm S threshold Target
    (outsideComponentOf_isOutsideComponent object windows stub.2 isStub.2.1) baseline
    (stateBound S)

/-- `X_cold`: the union of a family of windows. -/
noncomputable def windowsOf (family : Finset (Finset object.Vertex)) : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact family.biUnion id

theorem mem_windowsOf (family : Finset (Finset object.Vertex)) (vertex : object.Vertex) :
    vertex ∈ windowsOf object family ↔ ∃ window ∈ family, vertex ∈ window := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  simp [windowsOf]

/-- A selected half-edge of a family: its window endpoint lies in the family's
union and it is an edge. -/
theorem selected_facts (family : Finset (Finset object.Vertex))
    (stub : {stub // stub ∈ allSelectedStubs object family}) :
    stub.1.1 ∈ windowsOf object family ∧ object.graph.Adj stub.1.1 stub.1.2 := by
  classical
  obtain ⟨window, windowMem, stubMem⟩ := Finset.mem_biUnion.1 stub.2
  have isStub := mem_selectedStubs_isStub object stubMem
  exact ⟨(mem_windowsOf object family _).2 ⟨window, windowMem, isStub.1⟩, isStub.2.2⟩

/-- A third vertex exists once the object has more than two. -/
theorem exists_third (large : 2 < object.vertexCount) (left right : object.Vertex) :
    ∃ vertex, vertex ≠ left ∧ vertex ≠ right := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  have twoCard : (edgeSupport object left right).card <
      (Finset.univ : Finset object.Vertex).card := by
    refine lt_of_le_of_lt ?_ (show 2 < Finset.univ.card from by
      simpa [FiniteObject.vertexCount, FinEnum.card_eq_fintypeCard, Finset.card_univ] using large)
    letI : DecidableEq object.Vertex := object.vertices.decEq
    change ({left, right} : Finset object.Vertex).card ≤ 2
    exact Finset.card_le_two
  obtain ⟨vertex, _, notMem⟩ := Finset.exists_mem_notMem_of_card_lt_card twoCard
  refine ⟨vertex, fun h => notMem ?_, fun h => notMem ?_⟩
  · exact (mem_edgeSupport object _ _ vertex).2 (Or.inl h)
  · exact (mem_edgeSupport object _ _ vertex).2 (Or.inr h)

/-- The germ of a selected half-edge of a family of windows: the corridor germ
when the outside endpoint is in the outside graph, the edge germ when it lies in
another packed window. -/
noncomputable def stubGerm (family : Finset (Finset object.Vertex))
    (baseline : Graph.MinimumDegreeAtLeast threshold object)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    (large : 2 < object.vertexCount)
    (stub : {stub // stub ∈ allSelectedStubs object family}) :
    BoundedGerm S (Graph.MinimumDegreeAtLeast threshold) Target object := by
  classical
  exact if outsideAll : stub.1.2 ∈ windowsOf object family then
    edgeGerm S threshold Target object baseline (selected_facts object family stub).2
      (exists_third object large stub.1.1 stub.1.2)
  else
    corridorGerm S threshold Target object (windowsOf object family) baseline bridgeless
      ⟨(selected_facts object family stub).1, outsideAll, (selected_facts object family stub).2⟩

/-- **The candidate germ family**: the germs of the selected half-edges whose
support lies in the ambient-cubic part. -/
noncomputable def candidateGerms (family : Finset (Finset object.Vertex))
    (baseline : Graph.MinimumDegreeAtLeast threshold object)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    (large : 2 < object.vertexCount) :
    Finset (BoundedGerm S (Graph.MinimumDegreeAtLeast threshold) Target object) := by
  classical
  exact ((allSelectedStubs object family).attach.image
    (stubGerm S threshold Target object family baseline bridgeless large)).filter
    fun germ => ∀ vertex ∈ germ.support, object.degree vertex ≤ threshold


/-! ## `lem:cold-window-stub-excess`: an ambient-cubic window has `δ·order − 2(order−1)` stubs -/

section StubCount

variable (object : FiniteObject.{u})

open scoped Classical in
/-- The ordered adjacent pairs of the path graph on `n` vertices number
`2(n−1)`. -/
theorem card_pathGraph_adjPairs (n : Nat) :
    ((Finset.univ : Finset (Fin n × Fin n)).filter
      fun pair : Fin n × Fin n => (SimpleGraph.pathGraph n).Adj pair.1 pair.2).card =
      2 * (n - 1) := by
  classical
  cases n with
  | zero => simp
  | succ m =>
      let forward : Finset (Fin (m + 1) × Fin (m + 1)) :=
        (Finset.univ : Finset (Fin m)).image fun i =>
          (⟨i.1, by omega⟩, ⟨i.1 + 1, by omega⟩)
      let backward : Finset (Fin (m + 1) × Fin (m + 1)) :=
        (Finset.univ : Finset (Fin m)).image fun i =>
          (⟨i.1 + 1, by omega⟩, ⟨i.1, by omega⟩)
      have forwardCard : forward.card = m := by
        rw [Finset.card_image_of_injective]
        · simp
        · intro a b same
          simp only [Prod.mk.injEq, Fin.mk.injEq] at same
          exact Fin.ext same.1
      have backwardCard : backward.card = m := by
        rw [Finset.card_image_of_injective]
        · simp
        · intro a b same
          simp only [Prod.mk.injEq, Fin.mk.injEq] at same
          exact Fin.ext same.2
      have disjoint : Disjoint forward backward := by
        rw [Finset.disjoint_left]
        intro pair inForward inBackward
        simp only [forward, Finset.mem_image, Finset.mem_univ, true_and] at inForward
        simp only [backward, Finset.mem_image, Finset.mem_univ, true_and] at inBackward
        obtain ⟨i, rfl⟩ := inForward
        obtain ⟨j, same⟩ := inBackward
        simp only [Prod.mk.injEq, Fin.mk.injEq] at same
        omega
      have split : ((Finset.univ : Finset (Fin (m + 1) × Fin (m + 1))).filter
          fun pair : Fin (m + 1) × Fin (m + 1) =>
            (SimpleGraph.pathGraph (m + 1)).Adj pair.1 pair.2) = forward ∪ backward := by
        ext pair
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, forward,
          backward, Finset.mem_image, SimpleGraph.pathGraph_adj]
        constructor
        · rintro (h | h)
          · left
            refine ⟨⟨pair.1.1, by omega⟩, ?_⟩
            ext <;> simp [h]
          · right
            refine ⟨⟨pair.2.1, by omega⟩, ?_⟩
            ext <;> simp [h]
        · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
          · left; rfl
          · right; rfl
      rw [split, Finset.card_union_of_disjoint disjoint, forwardCard, backwardCard]
      omega

/-- **The external stubs of an ambient-cubic induced window** number
`δ·order − 2(order − 1)`; here the lower bound the count needs. -/
theorem stubCount_le_externalStubList_length {order threshold : Nat}
    (window : Finset object.Vertex)
    (induces : object.InducesWindow order window)
    (cubic : ∀ vertex ∈ window, object.degree vertex = threshold) :
    threshold * order ≤ (externalStubList object window).length + 2 * (order - 1) := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨⟨embedding⟩, cardinality⟩ := induces
  let inside : Finset (object.Vertex × object.Vertex) :=
    (window ×ˢ window).filter fun pair : object.Vertex × object.Vertex =>
      object.graph.Adj pair.1 pair.2
  let outside : Finset (object.Vertex × object.Vertex) :=
    (window ×ˢ Finset.univ).filter fun pair : object.Vertex × object.Vertex =>
      pair.2 ∉ window ∧ object.graph.Adj pair.1 pair.2
  have outsideCard : outside.card = (externalStubList object window).length := by
    rw [← List.toFinset_card_of_nodup (externalStubList_nodup object window)]
    apply congrArg Finset.card
    ext pair
    simp only [outside, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
      List.mem_toFinset, mem_externalStubList]
  have insideFibre : ∀ vertex ∈ window,
      (inside.filter fun pair : object.Vertex × object.Vertex => pair.1 = vertex) =
        ((object.graph.neighborFinset vertex).filter (· ∈ window)).image (Prod.mk vertex) := by
    intro vertex vertexMem
    ext pair
    simp only [inside, Finset.mem_filter, Finset.mem_product, Finset.mem_image,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨⟨⟨_, second⟩, adjacent⟩, rfl⟩
      exact ⟨pair.2, ⟨adjacent, second⟩, rfl⟩
    · rintro ⟨w, ⟨adjacent, second⟩, rfl⟩
      exact ⟨⟨⟨vertexMem, second⟩, adjacent⟩, rfl⟩
  have outsideFibre : ∀ vertex ∈ window,
      (outside.filter fun pair : object.Vertex × object.Vertex => pair.1 = vertex) =
        ((object.graph.neighborFinset vertex).filter (· ∉ window)).image (Prod.mk vertex) := by
    intro vertex vertexMem
    ext pair
    simp only [outside, Finset.mem_filter, Finset.mem_product, Finset.mem_image,
      SimpleGraph.mem_neighborFinset, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨⟨_, ⟨second, adjacent⟩⟩, rfl⟩
      exact ⟨pair.2, ⟨adjacent, second⟩, rfl⟩
    · rintro ⟨w, ⟨adjacent, second⟩, rfl⟩
      exact ⟨⟨vertexMem, ⟨second, adjacent⟩⟩, rfl⟩
  have degreeSplit :
      ∑ vertex ∈ window, object.degree vertex = inside.card + outside.card := by
    have insideSum : inside.card =
        ∑ vertex ∈ window, ((object.graph.neighborFinset vertex).filter (· ∈ window)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := window)]
      · refine Finset.sum_congr rfl fun vertex vertexMem => ?_
        rw [insideFibre vertex vertexMem,
          Finset.card_image_of_injective _ (Prod.mk_right_injective vertex)]
      · intro pair member
        exact (Finset.mem_product.1 (Finset.mem_filter.1 member).1).1
    have outsideSum : outside.card =
        ∑ vertex ∈ window, ((object.graph.neighborFinset vertex).filter (· ∉ window)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := window)]
      · refine Finset.sum_congr rfl fun vertex vertexMem => ?_
        rw [outsideFibre vertex vertexMem,
          Finset.card_image_of_injective _ (Prod.mk_right_injective vertex)]
      · intro pair member
        exact (Finset.mem_product.1 (Finset.mem_filter.1 member).1).1
    rw [insideSum, outsideSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun vertex _ => ?_
    have := Finset.card_filter_add_card_filter_not
      (s := object.graph.neighborFinset vertex) (p := (· ∈ window))
    rw [this]
    simp [FiniteObject.degree, SimpleGraph.card_neighborFinset_eq_degree]
  have insideCard : inside.card = 2 * (order - 1) := by
    rw [← card_pathGraph_adjPairs order]
    let toVertex : Fin order → object.Vertex := fun index => (embedding index).1
    have toVertexInj : Function.Injective toVertex := by
      intro a b same
      exact embedding.injective (Subtype.ext same)
    have toVertexRange : ∀ vertex ∈ window, ∃ index, toVertex index = vertex := by
      intro vertex member
      have imageCard : (Finset.univ.image toVertex).card = order := by
        rw [Finset.card_image_of_injective _ toVertexInj]; simp
      have imageSubset : Finset.univ.image toVertex ⊆ window := by
        intro v hv
        obtain ⟨index, _, rfl⟩ := Finset.mem_image.1 hv
        exact (embedding index).2
      have imageEq : Finset.univ.image toVertex = window :=
        Finset.eq_of_subset_of_card_le imageSubset (by rw [imageCard, cardinality])
      rw [← imageEq] at member
      obtain ⟨index, _, eq⟩ := Finset.mem_image.1 member
      exact ⟨index, eq⟩
    symm
    apply Finset.card_bij (fun (pair : Fin order × Fin order) _ =>
      (toVertex pair.1, toVertex pair.2))
    · intro pair member
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member
      simp only [inside, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨(embedding pair.1).2, (embedding pair.2).2⟩, embedding.map_adj_iff.2 member⟩
    · intro a _ b _ same
      simp only [Prod.mk.injEq] at same
      exact Prod.ext (toVertexInj same.1) (toVertexInj same.2)
    · intro pair member
      simp only [inside, Finset.mem_filter, Finset.mem_product] at member
      obtain ⟨i, hi⟩ := toVertexRange pair.1 member.1.1
      obtain ⟨j, hj⟩ := toVertexRange pair.2 member.1.2
      refine ⟨(i, j), ?_, by simp [hi, hj]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      apply embedding.map_adj_iff.1
      change object.graph.Adj (toVertex i) (toVertex j)
      rw [hi, hj]
      exact member.2
  have degreeConst : ∑ vertex ∈ window, object.degree vertex = threshold * order := by
    rw [Finset.sum_congr rfl cubic, Finset.sum_const, cardinality, smul_eq_mul, Nat.mul_comm]
  omega

end StubCount


/-! ### Supports of the germs of half-edges -/

/-- The corridor of a stub starts at the stub's foot. -/
theorem stubCorridor_entryStub (windows : Finset object.Vertex)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    {stub : object.Vertex × object.Vertex}
    (isStub : stub.1 ∈ windows ∧ stub.2 ∉ windows ∧ object.graph.Adj stub.1 stub.2) :
    (stubCorridor object windows bridgeless isStub).entryStub = (stub.2, stub.1) := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  simp only [Corridor.entryStub, stubCorridor, corridorOfOutsideComponent]
  exact List.idxOf_get _

theorem support_corridorGerm (windows : Finset object.Vertex)
    (baseline : Graph.MinimumDegreeAtLeast threshold object)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    {stub : object.Vertex × object.Vertex}
    (isStub : stub.1 ∈ windows ∧ stub.2 ∉ windows ∧ object.graph.Adj stub.1 stub.2) :
    (corridorGerm S threshold Target object windows baseline bridgeless isStub).support =
      (stubCorridor object windows bridgeless isStub).prefixSupport (stateBound S) := rfl

theorem foot_mem_support_corridorGerm (windows : Finset object.Vertex)
    (baseline : Graph.MinimumDegreeAtLeast threshold object)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    {stub : object.Vertex × object.Vertex}
    (isStub : stub.1 ∈ windows ∧ stub.2 ∉ windows ∧ object.graph.Adj stub.1 stub.2) :
    stub.2 ∈ (corridorGerm S threshold Target object windows baseline bridgeless
      isStub).support := by
  rw [support_corridorGerm]
  have := (stubCorridor object windows bridgeless isStub).foot_mem_prefixSupport (stateBound S)
  rwa [stubCorridor_entryStub] at this

theorem support_corridorGerm_card_le (windows : Finset object.Vertex)
    (baseline : Graph.MinimumDegreeAtLeast threshold object)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    {stub : object.Vertex × object.Vertex}
    (isStub : stub.1 ∈ windows ∧ stub.2 ∉ windows ∧ object.graph.Adj stub.1 stub.2) :
    (corridorGerm S threshold Target object windows baseline bridgeless isStub).support.card ≤
      stateBound S + 1 := by
  rw [support_corridorGerm]
  exact (stubCorridor object windows bridgeless isStub).prefixSupport_card_le _

theorem support_edgeGerm (baseline : Graph.MinimumDegreeAtLeast threshold object)
    {left right : object.Vertex} (adjacent : object.graph.Adj left right)
    (proper : ∃ vertex, vertex ≠ left ∧ vertex ≠ right) :
    (edgeGerm S threshold Target object baseline adjacent proper).support =
      edgeSupport object left right := rfl

/-- `Q_cold` is positive: the cut-state type is inhabited. -/
theorem one_le_stateBound : 1 ≤ stateBound S := by
  classical
  have : Nonempty (CutState S) :=
    ⟨{ boundaryDegrees := fun _ => ⟨0, Nat.succ_pos _⟩
       halfEdges := fun _ => ⟨0, Nat.succ_pos _⟩
       offsets := fun _ => ⟨0, S.windowOrder_pos⟩
       declared := fun _ _ => none }⟩
  exact Fintype.card_pos

/-- **The germ of a selected half-edge contains its outside endpoint and is
adjacent along the half-edge, and its support has at most `Q_cold + 1`
vertices.** -/
theorem stubGerm_facts (family : Finset (Finset object.Vertex))
    (baseline : Graph.MinimumDegreeAtLeast threshold object)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    (large : 2 < object.vertexCount)
    (stub : {stub // stub ∈ allSelectedStubs object family}) :
    stub.1.2 ∈ (stubGerm S threshold Target object family baseline bridgeless large stub).support ∧
      object.graph.Adj stub.1.2 stub.1.1 ∧
      (stubGerm S threshold Target object family baseline bridgeless large stub).support.card ≤
        stateBound S + 1 := by
  classical
  have facts := selected_facts object family stub
  refine ⟨?_, facts.2.symm, ?_⟩
  · unfold stubGerm
    split
    · rw [support_edgeGerm]
      exact (mem_edgeSupport object _ _ _).2 (Or.inr rfl)
    · exact foot_mem_support_corridorGerm S threshold Target object _ baseline bridgeless _
  · unfold stubGerm
    split
    · rw [support_edgeGerm]
      refine le_trans ?_ (Nat.succ_le_succ (one_le_stateBound S))
      letI : DecidableEq object.Vertex := object.vertices.decEq
      change ({stub.1.1, stub.1.2} : Finset object.Vertex).card ≤ 2
      exact Finset.card_le_two
    · exact support_corridorGerm_card_le S threshold Target object _ baseline bridgeless _


/-! ### The multiplicity of a candidate germ

A germ of a selected half-edge contains the outside endpoint of that half-edge,
so a candidate germ arises from at most `threshold · (Q_cold + 1)` half-edges:
its support has at most `Q_cold + 1` vertices, each of degree at most
`threshold`. -/

/-- The half-edges of a family whose germ is subcubic. -/
noncomputable def goodStubs (family : Finset (Finset object.Vertex))
    (baseline : Graph.MinimumDegreeAtLeast threshold object)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    (large : 2 < object.vertexCount) :
    Finset {stub // stub ∈ allSelectedStubs object family} := by
  classical
  exact (allSelectedStubs object family).attach.filter fun stub =>
    ∀ vertex ∈ (stubGerm S threshold Target object family baseline bridgeless large stub).support,
      object.degree vertex ≤ threshold

open scoped Classical in
theorem candidateGerms_eq_image (family : Finset (Finset object.Vertex))
    (baseline : Graph.MinimumDegreeAtLeast threshold object)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    (large : 2 < object.vertexCount) :
    candidateGerms S threshold Target object family baseline bridgeless large =
      (goodStubs S threshold Target object family baseline bridgeless large).image
        (stubGerm S threshold Target object family baseline bridgeless large) := by
  simp only [candidateGerms, goodStubs]
  rw [Finset.filter_image]

open scoped Classical in
theorem card_goodStubs_le (family : Finset (Finset object.Vertex))
    (baseline : Graph.MinimumDegreeAtLeast threshold object)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    (large : 2 < object.vertexCount) :
    (goodStubs S threshold Target object family baseline bridgeless large).card ≤
      threshold * (stateBound S + 1) *
        (candidateGerms S threshold Target object family baseline bridgeless large).card := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  rw [candidateGerms_eq_image]
  apply Finset.card_le_mul_card_image
  intro germ germMem
  obtain ⟨witness, witnessMem, rfl⟩ := Finset.mem_image.1 germMem
  have subcubic : ∀ vertex ∈ (stubGerm S threshold Target object family baseline bridgeless
      large witness).support, object.degree vertex ≤ threshold := by
    simp only [goodStubs, Finset.mem_filter] at witnessMem
    exact witnessMem.2
  -- the fibre injects into the half-edges rooted at a support vertex
  let target : Finset (object.Vertex × object.Vertex) :=
    (stubGerm S threshold Target object family baseline bridgeless large witness).support.biUnion
      fun u => (object.graph.neighborFinset u).image fun w => (w, u)
  have injects : ((goodStubs S threshold Target object family baseline bridgeless large).filter
      fun stub => stubGerm S threshold Target object family baseline bridgeless large stub =
        stubGerm S threshold Target object family baseline bridgeless large witness).card ≤
      target.card := by
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro stub stubMem
      simp only [Finset.mem_coe, Finset.mem_filter] at stubMem
      have facts := stubGerm_facts S threshold Target object family baseline bridgeless large stub
      rw [stubMem.2] at facts
      show stub.1 ∈ target
      refine Finset.mem_biUnion.2 ⟨stub.1.2, facts.1, ?_⟩
      exact Finset.mem_image.2 ⟨stub.1.1, (SimpleGraph.mem_neighborFinset _ _ _).2 facts.2.1, rfl⟩
    · intro a _ b _ same
      exact Subtype.ext same
  refine injects.trans ?_
  refine (Finset.card_biUnion_le).trans ?_
  have each : ∀ u ∈ (stubGerm S threshold Target object family baseline bridgeless large
      witness).support,
      ((object.graph.neighborFinset u).image fun w => (w, u)).card ≤ threshold := by
    intro u uMem
    refine Finset.card_image_le.trans ?_
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact subcubic u uMem
  calc (∑ u ∈ (stubGerm S threshold Target object family baseline bridgeless large
          witness).support, ((object.graph.neighborFinset u).image fun w => (w, u)).card)
      ≤ ∑ _u ∈ (stubGerm S threshold Target object family baseline bridgeless large
          witness).support, threshold := Finset.sum_le_sum each
    _ = (stubGerm S threshold Target object family baseline bridgeless large
          witness).support.card * threshold := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (stateBound S + 1) * threshold :=
        Nat.mul_le_mul_right _
          (stubGerm_facts S threshold Target object family baseline bridgeless large witness).2.2
    _ = threshold * (stateBound S + 1) := Nat.mul_comm _ _


/-! ### The overlap bound, `lem:cold-germ-extraction`

*"A fixed vertex belongs to the support of at most `B_cold` candidate germs.  A
fixed candidate support has at most `M_cold` vertices, so it meets at most
`M_cold·B_cold` other candidate supports."* -/

/-- The subcubic vertices of the object. -/
noncomputable def cubicVertices (bound : Nat) : Finset object.Vertex := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  exact Finset.univ.filter fun vertex => object.degree vertex ≤ bound

theorem mem_cubicVertices (bound : Nat) (vertex : object.Vertex) :
    vertex ∈ cubicVertices object bound ↔ object.degree vertex ≤ bound := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  simp [cubicVertices]

/-- The subcubic reach of the object's graph, with the object's own instances. -/
noncomputable def objectReach (bound : Nat) (v : object.Vertex) (r : Nat) :
    Finset object.Vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := inferInstance
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact SubcubicReach.reach object.graph (cubicVertices object bound) v r v

theorem card_objectReach_le (v : object.Vertex) (r : Nat) :
    (objectReach object 3 v r).card ≤ 1 + 3 * (2 ^ r - 1) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := inferInstance
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  apply SubcubicReach.card_reach_le
  intro z zMem
  have := (mem_cubicVertices object 3 z).1 zMem
  simpa [FiniteObject.degree] using this

theorem mem_objectReach (bound : Nat) (v : object.Vertex) (r : Nat) (w : object.Vertex) :
    w ∈ objectReach object bound v r ↔
      ∃ p : object.graph.Walk v w, p.IsPath ∧ p.length ≤ r ∧
        (∀ z ∈ p.support.dropLast, z ∈ cubicVertices object bound) ∧
        (∀ hp : ¬ p.Nil, p.getVert 1 ≠ v) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := inferInstance
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact SubcubicReach.mem_reach object.graph

/-- **A vertex of a subcubic corridor prefix reaches the corridor's foot** by a
subcubic path of length at most the prefix length. -/
theorem foot_mem_objectReach_of_mem_prefixSupport {windows component : Finset object.Vertex}
    (corridor : Corridor object windows component) (n : Nat) (bound : Nat)
    (subcubic : ∀ vertex ∈ corridor.prefixSupport n, object.degree vertex ≤ bound)
    {v : object.Vertex} (member : v ∈ corridor.prefixSupport n) :
    corridor.entryStub.1 ∈ objectReach object bound v n := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  obtain ⟨inner, innerMem, rfl⟩ := (corridor.mem_prefixSupport n v).1 member
  let walk := corridor.inside.1.take n
  let embedding := object.induceEmbedding component
  have walkPath : walk.IsPath := corridor.inside.2.take n
  let toInner := walk.takeUntil inner innerMem
  let mapped := (toInner.map embedding.toHom).reverse
  have mappedPath : mapped.IsPath :=
    ((SimpleGraph.Walk.map_isPath_iff_of_injective embedding.injective).2
      (walkPath.takeUntil innerMem)).reverse
  have mappedSupport : ∀ z ∈ mapped.support, z ∈ corridor.prefixSupport n := by
    intro z zMem
    simp only [mapped, SimpleGraph.Walk.support_reverse, List.mem_reverse,
      SimpleGraph.Walk.support_map, List.mem_map] at zMem
    obtain ⟨y, yMem, rfl⟩ := zMem
    exact (corridor.mem_prefixSupport n _).2
      ⟨y, walk.support_takeUntil_subset_support innerMem yMem, rfl⟩
  have mappedLength : mapped.length ≤ n := by
    simp only [mapped, SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_map]
    refine (SimpleGraph.Walk.length_takeUntil_le_length walk innerMem).trans ?_
    simp [walk]
  have footEq : embedding (stubFoot object windows component corridor.entry) =
      corridor.entryStub.1 := rfl
  let final := mapped.copy rfl footEq
  have finalPath : final.IsPath := (SimpleGraph.Walk.isPath_copy _ _ _).2 mappedPath
  show corridor.entryStub.1 ∈ SubcubicReach.reach object.graph (cubicVertices object bound) inner.1 n inner.1
  refine (SubcubicReach.mem_reach object.graph).2 ⟨final, finalPath, ?_, ?_, ?_⟩
  · show (mapped.copy rfl footEq).length ≤ n
    rw [SimpleGraph.Walk.length_copy]
    exact mappedLength
  · intro z zMem
    change z ∈ (mapped.copy rfl footEq).support.dropLast at zMem
    rw [SimpleGraph.Walk.support_copy] at zMem
    exact (mem_cubicVertices object bound z).2
      (subcubic z (mappedSupport z (List.mem_of_mem_dropLast zMem)))
  · intro notNil same
    have := (finalPath.getVert_eq_start_iff_of_not_nil (i := 1) notNil).1 same
    exact absurd this (by decide)


/-- The half-edges rooted at a vertex of a candidate germ containing `v`: the
half-edges whose foot is a subcubic vertex reached from `v` within `Q_cold`
steps, and the half-edges at `v` itself. -/
noncomputable def germsThrough (v : object.Vertex) (radius : Nat) :
    Finset (object.Vertex × object.Vertex) := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact (((objectReach object 3 v radius).filter fun u => object.degree u ≤ 3).biUnion
      fun u => (object.graph.neighborFinset u).image fun w => (w, u)) ∪
    ((object.graph.neighborFinset v).image fun u => (v, u)) ∪
    ((object.graph.neighborFinset v).image fun w => (w, v))

theorem card_germsThrough_le (v : object.Vertex) (radius : Nat)
    (cubic : object.degree v ≤ 3) :
    (germsThrough object v radius).card ≤ 3 * (1 + 3 * (2 ^ radius - 1)) + 6 := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have degreeCard : (object.graph.neighborFinset v).card ≤ 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact cubic
  have hA : (((objectReach object 3 v radius).filter fun u => object.degree u ≤ 3).biUnion
      fun u => (object.graph.neighborFinset u).image fun w => (w, u)).card ≤
      3 * (1 + 3 * (2 ^ radius - 1)) := by
    refine (Finset.card_biUnion_le).trans ?_
    have each : ∀ u ∈ (objectReach object 3 v radius).filter fun u => object.degree u ≤ 3,
        ((object.graph.neighborFinset u).image fun w => (w, u)).card ≤ 3 := by
      intro u uMem
      refine Finset.card_image_le.trans ?_
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact (Finset.mem_filter.1 uMem).2
    calc (∑ u ∈ (objectReach object 3 v radius).filter (fun u => object.degree u ≤ 3),
          ((object.graph.neighborFinset u).image fun w => (w, u)).card)
        ≤ ∑ _u ∈ (objectReach object 3 v radius).filter (fun u => object.degree u ≤ 3), 3 :=
          Finset.sum_le_sum each
      _ = ((objectReach object 3 v radius).filter (fun u => object.degree u ≤ 3)).card * 3 := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (1 + 3 * (2 ^ radius - 1)) * 3 :=
          Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans
            (card_objectReach_le object v radius))
      _ = 3 * (1 + 3 * (2 ^ radius - 1)) := Nat.mul_comm _ _
  have hB : ((object.graph.neighborFinset v).image fun u => (v, u)).card ≤ 3 :=
    Finset.card_image_le.trans degreeCard
  have hC : ((object.graph.neighborFinset v).image fun w => (w, v)).card ≤ 3 :=
    Finset.card_image_le.trans degreeCard
  simp only [germsThrough]
  refine (Finset.card_union_le _ _).trans ?_
  refine le_trans (Nat.add_le_add (Finset.card_union_le _ _) le_rfl) ?_
  omega

/-- A good half-edge whose germ contains `v` is rooted in `germsThrough v Q`. -/
theorem stub_mem_germsThrough (family : Finset (Finset object.Vertex))
    (baseline : Graph.MinimumDegreeAtLeast 3 object)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    (large : 2 < object.vertexCount)
    (stub : {stub // stub ∈ allSelectedStubs object family})
    (good : ∀ vertex ∈ (stubGerm S 3 Target object family baseline bridgeless large stub).support,
      object.degree vertex ≤ 3)
    {v : object.Vertex}
    (member : v ∈ (stubGerm S 3 Target object family baseline bridgeless large stub).support) :
    stub.1 ∈ germsThrough object v (stateBound S) := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have facts := selected_facts object family stub
  simp only [germsThrough, Finset.mem_union]
  by_cases outsideAll : stub.1.2 ∈ windowsOf object family
  · rw [stubGerm, dif_pos outsideAll, support_edgeGerm] at member
    rcases (mem_edgeSupport object _ _ v).1 member with rfl | rfl
    · left; right
      exact Finset.mem_image.2 ⟨stub.1.2, (SimpleGraph.mem_neighborFinset _ _ _).2 facts.2,
        Prod.mk.eta⟩
    · right
      exact Finset.mem_image.2 ⟨stub.1.1, (SimpleGraph.mem_neighborFinset _ _ _).2 facts.2.symm,
        Prod.mk.eta⟩
  · rw [stubGerm, dif_neg outsideAll] at member good
    rw [support_corridorGerm] at member good
    left; left
    refine Finset.mem_biUnion.2 ⟨stub.1.2, ?_, ?_⟩
    · refine Finset.mem_filter.2 ⟨?_, ?_⟩
      · have := foot_mem_objectReach_of_mem_prefixSupport object
          (stubCorridor object (windowsOf object family) bridgeless _) (stateBound S) 3 good member
        rwa [stubCorridor_entryStub] at this
      · exact good _ (by
          rw [← support_corridorGerm]
          exact foot_mem_support_corridorGerm S 3 Target object _ baseline bridgeless _)
    · exact Finset.mem_image.2 ⟨stub.1.1, (SimpleGraph.mem_neighborFinset _ _ _).2 facts.2.symm,
        Prod.mk.eta⟩

set_option maxHeartbeats 1600000 in
open scoped Classical in
/-- **The overlap bound of `lem:cold-germ-extraction`**: a candidate germ meets at
most `M_cold · B_cold` candidate germs (itself included). -/
theorem candidateGerms_overlap_le (family : Finset (Finset object.Vertex))
    (baseline : Graph.MinimumDegreeAtLeast 3 object)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    (large : 2 < object.vertexCount)
    (germ : BoundedGerm S (Graph.MinimumDegreeAtLeast 3) Target object)
    (germMem : germ ∈ candidateGerms S 3 Target object family baseline bridgeless large) :
    ((candidateGerms S 3 Target object family baseline bridgeless large).filter
      fun other => ¬ Disjoint germ.support other.support).card ≤
      exchangeBound S * overlapBound 3 S := by
  have germSubcubic : ∀ vertex ∈ germ.support, object.degree vertex ≤ 3 := by
    simp only [candidateGerms, Finset.mem_filter] at germMem
    exact germMem.2
  have germMemImage := germMem
  rw [candidateGerms_eq_image] at germMemImage
  obtain ⟨witness, _, witnessEq⟩ := Finset.mem_image.1 germMemImage
  have supportCard : germ.support.card ≤ stateBound S + 1 := by
    rw [← witnessEq]
    exact (stubGerm_facts S 3 Target object family baseline bridgeless large witness).2.2
  have perVertex : ∀ v ∈ germ.support,
      ((candidateGerms S 3 Target object family baseline bridgeless large).filter
        fun other => v ∈ other.support).card ≤
        3 * (1 + 3 * (2 ^ stateBound S - 1)) + 6 := by
    intro v vMem
    rw [candidateGerms_eq_image, Finset.filter_image]
    refine Finset.card_image_le.trans ?_
    refine le_trans ?_ (card_germsThrough_le object v (stateBound S) (germSubcubic v vMem))
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro stub stubMem
      simp only [Finset.mem_coe, Finset.mem_filter, goodStubs] at stubMem
      exact stub_mem_germsThrough S Target object family baseline bridgeless large stub
        stubMem.1.2 stubMem.2
    · intro a _ b _ same
      exact Subtype.ext same
  have cover : ((candidateGerms S 3 Target object family baseline bridgeless large).filter
      fun other => ¬ Disjoint germ.support other.support) ⊆
      germ.support.biUnion fun v =>
        (candidateGerms S 3 Target object family baseline bridgeless large).filter
          fun other => v ∈ other.support := by
    intro other otherMem
    rw [Finset.mem_filter] at otherMem
    obtain ⟨v, vGerm, vOther⟩ := Finset.not_disjoint_iff.1 otherMem.2
    exact Finset.mem_biUnion.2 ⟨v, vGerm, Finset.mem_filter.2 ⟨otherMem.1, vOther⟩⟩
  have summed : (germ.support.biUnion fun v =>
      (candidateGerms S 3 Target object family baseline bridgeless large).filter
        fun other => v ∈ other.support).card ≤
      (stateBound S + 1) * (3 * (1 + 3 * (2 ^ stateBound S - 1)) + 6) := by
    refine Finset.card_biUnion_le.trans ?_
    calc (∑ v ∈ germ.support,
          ((candidateGerms S 3 Target object family baseline bridgeless large).filter
            fun other => v ∈ other.support).card)
        ≤ ∑ _v ∈ germ.support, (3 * (1 + 3 * (2 ^ stateBound S - 1)) + 6) :=
          Finset.sum_le_sum perVertex
      _ = germ.support.card * (3 * (1 + 3 * (2 ^ stateBound S - 1)) + 6) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (stateBound S + 1) * (3 * (1 + 3 * (2 ^ stateBound S - 1)) + 6) :=
          Nat.mul_le_mul_right _ supportCard
  have arithmetic : (stateBound S + 1) * (3 * (1 + 3 * (2 ^ stateBound S - 1)) + 6) ≤
      exchangeBound S * overlapBound 3 S := by
    have onePow : 1 ≤ 2 ^ stateBound S := Nat.one_le_two_pow
    have grow : 4 * 2 ^ stateBound S ≤ 2 ^ (exchangeBound S + 2) := by
      rw [show 4 * 2 ^ stateBound S = 2 ^ (stateBound S + 2) by ring]
      exact Nat.pow_le_pow_right (by norm_num) (by unfold exchangeBound; omega)
    have orderPos := S.windowOrder_pos
    have stubExcessGe : 3 ≤ stubExcess 3 S := by unfold stubExcess; omega
    have exchangeGe : stateBound S + 1 ≤ exchangeBound S := by
      unfold exchangeBound interfaceBudget; omega
    unfold overlapBound
    have inner : 3 * (1 + 3 * (2 ^ stateBound S - 1)) + 6 ≤
        3 * (1 + 3 * (2 ^ (exchangeBound S + 2) - 1)) := by omega
    calc (stateBound S + 1) * (3 * (1 + 3 * (2 ^ stateBound S - 1)) + 6)
        ≤ exchangeBound S * (3 * (1 + 3 * (2 ^ (exchangeBound S + 2) - 1))) :=
          Nat.mul_le_mul exchangeGe inner
      _ ≤ exchangeBound S * (stubExcess 3 S * (1 + 3 * (2 ^ (exchangeBound S + 2) - 1))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ stubExcessGe)
  exact ((Finset.card_le_card cover).trans summed).trans arithmetic


/-! ### The high-degree loss

*"If a candidate support contains a vertex of degree at least `4`, then the
corresponding corridor first enters the high-degree handoff ledger and was
already removed."*  The half-edges lost this way are charged to the degree
surplus: a corridor prefix that meets a high-degree vertex `h` reaches it from
its foot through subcubic vertices, so its foot lies within `Q_cold` steps of a
neighbour of `h`, and `Σ_{deg h ≥ 4} deg h ≤ 4·σ(G)`. -/

/-- The vertices of degree above `3`. -/
noncomputable def highVertices : Finset object.Vertex := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  exact Finset.univ.filter fun vertex => 3 < object.degree vertex

theorem mem_highVertices (vertex : object.Vertex) :
    vertex ∈ highVertices object ↔ 3 < object.degree vertex := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  simp [highVertices]

/-- `Σ_{deg h ≥ 4} deg h ≤ 4·σ(G)` at baseline `3`. -/
theorem sum_highVertices_degree_le (baseline : Graph.MinimumDegreeAtLeast 3 object) :
    ∑ h ∈ highVertices object, object.degree h ≤ 4 * object.degreeSurplus 3 := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have handshake : (∑ vertex : object.Vertex, object.degree vertex) = 2 * object.edgeCount := by
    simpa [FiniteObject.degree, FiniteObject.edgeCount] using
      object.graph.sum_degrees_eq_twice_card_edges
  have lower : ∀ vertex : object.Vertex, 3 ≤ object.degree vertex := fun vertex =>
    le_trans baseline (object.minDegree_le_degree vertex)
  have count : (∑ _vertex : object.Vertex, 3) = 3 * object.vertexCount := by
    simp [Finset.sum_const, Finset.card_univ, FiniteObject.vertexCount,
      FinEnum.card_eq_fintypeCard, Nat.mul_comm]
  -- `Σ_v (deg v − 3) = σ`
  have surplus : (∑ vertex : object.Vertex, (object.degree vertex - 3)) = object.degreeSurplus 3 := by
    unfold FiniteObject.degreeSurplus
    rw [← handshake, ← count, ← Finset.sum_tsub_distrib]
    intro vertex _
    exact lower vertex
  have highPart : (∑ h ∈ highVertices object, (object.degree h - 3)) ≤
      ∑ vertex : object.Vertex, (object.degree vertex - 3) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  have each : ∀ h ∈ highVertices object, object.degree h ≤ 4 * (object.degree h - 3) := by
    intro h hMem
    have := (mem_highVertices object h).1 hMem
    omega
  calc (∑ h ∈ highVertices object, object.degree h)
      ≤ ∑ h ∈ highVertices object, 4 * (object.degree h - 3) := Finset.sum_le_sum each
    _ = 4 * ∑ h ∈ highVertices object, (object.degree h - 3) := by rw [Finset.mul_sum]
    _ ≤ 4 * object.degreeSurplus 3 := by
        rw [← surplus]
        exact Nat.mul_le_mul_left _ highPart

/-- The half-edges charged to a high-degree vertex `h`: those with foot `h`, and
those whose foot is a subcubic vertex within `Q_cold` steps of a neighbour of
`h`. -/
noncomputable def lostThrough (h : object.Vertex) (radius : Nat) :
    Finset (object.Vertex × object.Vertex) := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact ((object.graph.neighborFinset h).image fun w => (w, h)) ∪
    (object.graph.neighborFinset h).biUnion fun y =>
      ((objectReach object 3 y radius).filter fun u => object.degree u ≤ 3).biUnion
        fun u => (object.graph.neighborFinset u).image fun w => (w, u)

theorem card_lostThrough_le (h : object.Vertex) (radius : Nat) :
    (lostThrough object h radius).card ≤ object.degree h * (1 + 3 * (1 + 3 * (2 ^ radius - 1))) := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have degreeCard : (object.graph.neighborFinset h).card = object.degree h := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; rfl
  have inner : ∀ y, (((objectReach object 3 y radius).filter fun u => object.degree u ≤ 3).biUnion
      fun u => (object.graph.neighborFinset u).image fun w => (w, u)).card ≤
      3 * (1 + 3 * (2 ^ radius - 1)) := by
    intro y
    refine (Finset.card_biUnion_le).trans ?_
    have each : ∀ u ∈ (objectReach object 3 y radius).filter fun u => object.degree u ≤ 3,
        ((object.graph.neighborFinset u).image fun w => (w, u)).card ≤ 3 := by
      intro u uMem
      refine Finset.card_image_le.trans ?_
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact (Finset.mem_filter.1 uMem).2
    calc (∑ u ∈ (objectReach object 3 y radius).filter (fun u => object.degree u ≤ 3),
          ((object.graph.neighborFinset u).image fun w => (w, u)).card)
        ≤ ∑ _u ∈ (objectReach object 3 y radius).filter (fun u => object.degree u ≤ 3), 3 :=
          Finset.sum_le_sum each
      _ = ((objectReach object 3 y radius).filter (fun u => object.degree u ≤ 3)).card * 3 := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (1 + 3 * (2 ^ radius - 1)) * 3 :=
          Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans
            (card_objectReach_le object y radius))
      _ = 3 * (1 + 3 * (2 ^ radius - 1)) := Nat.mul_comm _ _
  simp only [lostThrough]
  refine (Finset.card_union_le _ _).trans ?_
  have first : ((object.graph.neighborFinset h).image fun w => (w, h)).card ≤ object.degree h :=
    Finset.card_image_le.trans (le_of_eq degreeCard)
  have second : ((object.graph.neighborFinset h).biUnion fun y =>
      ((objectReach object 3 y radius).filter fun u => object.degree u ≤ 3).biUnion
        fun u => (object.graph.neighborFinset u).image fun w => (w, u)).card ≤
      object.degree h * (3 * (1 + 3 * (2 ^ radius - 1))) := by
    refine (Finset.card_biUnion_le).trans ?_
    calc (∑ y ∈ object.graph.neighborFinset h,
          (((objectReach object 3 y radius).filter fun u => object.degree u ≤ 3).biUnion
            fun u => (object.graph.neighborFinset u).image fun w => (w, u)).card)
        ≤ ∑ _y ∈ object.graph.neighborFinset h, 3 * (1 + 3 * (2 ^ radius - 1)) :=
          Finset.sum_le_sum fun y _ => inner y
      _ = object.degree h * (3 * (1 + 3 * (2 ^ radius - 1))) := by
          rw [Finset.sum_const, smul_eq_mul, degreeCard]
  calc ((object.graph.neighborFinset h).image fun w => (w, h)).card +
        ((object.graph.neighborFinset h).biUnion fun y =>
          ((objectReach object 3 y radius).filter fun u => object.degree u ≤ 3).biUnion
            fun u => (object.graph.neighborFinset u).image fun w => (w, u)).card
      ≤ object.degree h + object.degree h * (3 * (1 + 3 * (2 ^ radius - 1))) :=
        Nat.add_le_add first second
    _ = object.degree h * (1 + 3 * (1 + 3 * (2 ^ radius - 1))) := by ring


set_option maxHeartbeats 1600000 in
/-- **A corridor prefix that meets a high-degree vertex is charged to it**: with
`h` the first high vertex along the prefix, either the foot is `h`, or the foot
is subcubic and within `Q_cold` steps of the neighbour of `h` preceding it. -/
theorem stub_mem_lostThrough_of_high {windows component : Finset object.Vertex}
    (corridor : Corridor object windows component) (n : Nat)
    (high : ∃ vertex ∈ corridor.prefixSupport n, 3 < object.degree vertex) :
    ∃ h ∈ highVertices object,
      (corridor.entryStub.2, corridor.entryStub.1) ∈ lostThrough object h n := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  let embedding := object.induceEmbedding component
  let walk := (corridor.inside.1.take n).map embedding.toHom
  have walkPath : walk.IsPath :=
    (SimpleGraph.Walk.map_isPath_iff_of_injective embedding.injective).2 (corridor.inside.2.take n)
  have walkLength : walk.length ≤ n := by
    simp [walk]
  have supportEq : ∀ vertex, vertex ∈ walk.support ↔ vertex ∈ corridor.prefixSupport n := by
    intro vertex
    rw [corridor.mem_prefixSupport n vertex]
    simp only [walk, SimpleGraph.Walk.support_map, List.mem_map]
    rfl
  have startEq : walk.getVert 0 = corridor.entryStub.1 := by
    rw [SimpleGraph.Walk.getVert_zero]; rfl
  have footEq : embedding.toHom (stubFoot object windows component corridor.entry) =
      corridor.entryStub.1 := rfl
  clear_value walk
  -- the first index at which the prefix is high
  obtain ⟨vertex, vertexMem, vertexHigh⟩ := high
  have exists_index : ∃ i, i ≤ walk.length ∧ 3 < object.degree (walk.getVert i) := by
    obtain ⟨i, iEq, iLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.1 ((supportEq vertex).2 vertexMem)
    exact ⟨i, iLe, by rw [iEq]; exact vertexHigh⟩
  have iSpec := Nat.find_spec exists_index
  have iMin : ∀ k < Nat.find exists_index,
      ¬ (k ≤ walk.length ∧ 3 < object.degree (walk.getVert k)) :=
    fun k kLt => Nat.find_min exists_index kLt
  generalize hi : Nat.find exists_index = i at iSpec iMin
  have low : ∀ k < i, object.degree (walk.getVert k) ≤ 3 := by
    intro k kLt
    have := iMin k kLt
    have kLe : k ≤ walk.length := le_trans (le_of_lt kLt) iSpec.1
    by_contra notLow
    exact this ⟨kLe, lt_of_not_ge notLow⟩
  refine ⟨walk.getVert i, (mem_highVertices object _).2 iSpec.2, ?_⟩
  have adjFoot : object.graph.Adj corridor.entryStub.1 corridor.entryStub.2 :=
    ((mem_boundaryStubs_iff object windows component _).1
      (List.get_mem _ corridor.entry)).2.2
  simp only [lostThrough, Finset.mem_union]
  cases i with
  | zero =>
      left
      rw [startEq]
      exact Finset.mem_image.2 ⟨corridor.entryStub.2,
        (SimpleGraph.mem_neighborFinset _ _ _).2 adjFoot, rfl⟩
  | succ j =>
      right
      have jLt : j < walk.length := by have := iSpec.1; omega
      refine Finset.mem_biUnion.2 ⟨walk.getVert j, ?_, ?_⟩
      · rw [SimpleGraph.mem_neighborFinset]
        exact (walk.adj_getVert_succ jLt).symm
      · refine Finset.mem_biUnion.2 ⟨corridor.entryStub.1, ?_, ?_⟩
        · refine Finset.mem_filter.2 ⟨?_, ?_⟩
          · rw [mem_objectReach]
            let back := (walk.take j).reverse
            have backPath : back.IsPath := (walkPath.take j).reverse
            have backLength : back.length ≤ n := by
              simp only [back, SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.take_length]
              omega
            have backSupport : ∀ z ∈ back.support, ∃ k ≤ j, walk.getVert k = z := by
              intro z zMem
              simp only [back, SimpleGraph.Walk.support_reverse, List.mem_reverse] at zMem
              obtain ⟨k, kEq, kLe⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 zMem
              rw [SimpleGraph.Walk.take_length] at kLe
              have kLeJ : k ≤ j := le_trans kLe (min_le_left _ _)
              refine ⟨k, kLeJ, ?_⟩
              rw [← kEq, SimpleGraph.Walk.take_getVert, min_eq_right kLeJ]
            let final := back.copy rfl footEq
            have finalPath : final.IsPath := (SimpleGraph.Walk.isPath_copy _ _ _).2 backPath
            refine ⟨final, finalPath, ?_, ?_, ?_⟩
            · show (back.copy rfl footEq).length ≤ n
              rw [SimpleGraph.Walk.length_copy]; exact backLength
            · intro z zMem
              change z ∈ (back.copy rfl footEq).support.dropLast at zMem
              rw [SimpleGraph.Walk.support_copy] at zMem
              obtain ⟨k, kLe, kEq⟩ := backSupport z (List.mem_of_mem_dropLast zMem)
              rw [← kEq]
              exact (mem_cubicVertices object 3 _).2 (low k (by omega))
            · intro notNil same
              have := (finalPath.getVert_eq_start_iff_of_not_nil (i := 1) notNil).1 same
              exact absurd this (by decide)
          · rw [← startEq]
            exact low 0 (by omega)
        · exact Finset.mem_image.2 ⟨corridor.entryStub.2,
            (SimpleGraph.mem_neighborFinset _ _ _).2 adjFoot, rfl⟩


/-- The half-edges of a family whose germ is not subcubic. -/
noncomputable def badStubs (family : Finset (Finset object.Vertex))
    (baseline : Graph.MinimumDegreeAtLeast threshold object)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    (large : 2 < object.vertexCount) :
    Finset {stub // stub ∈ allSelectedStubs object family} := by
  classical
  exact (allSelectedStubs object family).attach.filter fun stub =>
    ¬ ∀ vertex ∈ (stubGerm S threshold Target object family baseline bridgeless large
      stub).support, object.degree vertex ≤ threshold

theorem card_good_add_card_bad (family : Finset (Finset object.Vertex))
    (baseline : Graph.MinimumDegreeAtLeast threshold object)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    (large : 2 < object.vertexCount) :
    (goodStubs S threshold Target object family baseline bridgeless large).card +
      (badStubs S threshold Target object family baseline bridgeless large).card =
      (allSelectedStubs object family).card := by
  classical
  simp only [goodStubs, badStubs]
  rw [Finset.card_filter_add_card_filter_not, Finset.card_attach]

/-- **The high-degree loss**: at ambient-cubic windows, the half-edges whose germ
meets a vertex of degree above three number at most `B_cold · σ(G)`. -/
theorem card_badStubs_le (family : Finset (Finset object.Vertex))
    (baseline : Graph.MinimumDegreeAtLeast 3 object)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    (large : 2 < object.vertexCount)
    (windowsCubic : ∀ w ∈ windowsOf object family, object.degree w = 3) :
    (badStubs S 3 Target object family baseline bridgeless large).card ≤
      overlapBound 3 S * object.degreeSurplus 3 := by
  classical
  -- every bad half-edge is charged to a high vertex
  have charged : ∀ stub ∈ badStubs S 3 Target object family baseline bridgeless large,
      stub.1 ∈ (highVertices object).biUnion fun h => lostThrough object h (stateBound S) := by
    intro stub stubMem
    simp only [badStubs, Finset.mem_filter] at stubMem
    have notGood := stubMem.2
    have facts := selected_facts object family stub
    by_cases outsideAll : stub.1.2 ∈ windowsOf object family
    · exfalso
      apply notGood
      rw [stubGerm, dif_pos outsideAll, support_edgeGerm]
      intro vertex vertexMem
      rcases (mem_edgeSupport object _ _ vertex).1 vertexMem with rfl | rfl
      · exact le_of_eq (windowsCubic _ facts.1)
      · exact le_of_eq (windowsCubic _ outsideAll)
    · rw [stubGerm, dif_neg outsideAll, support_corridorGerm] at notGood
      have high : ∃ vertex ∈ (stubCorridor object (windowsOf object family) bridgeless
          ⟨facts.1, outsideAll, facts.2⟩).prefixSupport (stateBound S),
          3 < object.degree vertex := by
        by_contra none
        apply notGood
        intro vertex vertexMem
        by_contra tooHigh
        exact none ⟨vertex, vertexMem, lt_of_not_ge tooHigh⟩
      obtain ⟨h, hMem, lost⟩ := stub_mem_lostThrough_of_high object _ (stateBound S) high
      rw [stubCorridor_entryStub] at lost
      exact Finset.mem_biUnion.2 ⟨h, hMem, lost⟩
  have injects : (badStubs S 3 Target object family baseline bridgeless large).card ≤
      ((highVertices object).biUnion fun h => lostThrough object h (stateBound S)).card := by
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro stub stubMem
      exact charged stub stubMem
    · intro a _ b _ same
      exact Subtype.ext same
  refine injects.trans ?_
  refine (Finset.card_biUnion_le).trans ?_
  have factor : ∀ h ∈ highVertices object,
      (lostThrough object h (stateBound S)).card ≤
        object.degree h * (1 + 3 * (1 + 3 * (2 ^ stateBound S - 1))) :=
    fun h _ => card_lostThrough_le object h (stateBound S)
  calc (∑ h ∈ highVertices object, (lostThrough object h (stateBound S)).card)
      ≤ ∑ h ∈ highVertices object, object.degree h * (1 + 3 * (1 + 3 * (2 ^ stateBound S - 1))) :=
        Finset.sum_le_sum factor
    _ = (∑ h ∈ highVertices object, object.degree h) * (1 + 3 * (1 + 3 * (2 ^ stateBound S - 1))) := by
        rw [Finset.sum_mul]
    _ ≤ (4 * object.degreeSurplus 3) * (1 + 3 * (1 + 3 * (2 ^ stateBound S - 1))) :=
        Nat.mul_le_mul_right _ (sum_highVertices_degree_le object baseline)
    _ ≤ overlapBound 3 S * object.degreeSurplus 3 := by
        have onePow : 1 ≤ 2 ^ stateBound S := Nat.one_le_two_pow
        have grow : 4 * 2 ^ stateBound S ≤ 2 ^ (exchangeBound S + 2) := by
          rw [show 4 * 2 ^ stateBound S = 2 ^ (stateBound S + 2) by ring]
          exact Nat.pow_le_pow_right (by norm_num) (by unfold exchangeBound; omega)
        have orderPos := S.windowOrder_pos
        have stubExcessGe : 3 ≤ stubExcess 3 S := by unfold stubExcess; omega
        unfold overlapBound
        have inner : 4 * (1 + 3 * (1 + 3 * (2 ^ stateBound S - 1))) ≤
            3 * (1 + 3 * (2 ^ (exchangeBound S + 2) - 1)) := by omega
        calc 4 * object.degreeSurplus 3 * (1 + 3 * (1 + 3 * (2 ^ stateBound S - 1)))
            = (4 * (1 + 3 * (1 + 3 * (2 ^ stateBound S - 1)))) * object.degreeSurplus 3 := by ring
          _ ≤ (3 * (1 + 3 * (2 ^ (exchangeBound S + 2) - 1))) * object.degreeSurplus 3 :=
              Nat.mul_le_mul_right _ inner
          _ ≤ (stubExcess 3 S * (1 + 3 * (2 ^ (exchangeBound S + 2) - 1))) *
                object.degreeSurplus 3 :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ stubExcessGe)

/-- **`lem:cold-germ-extraction`, the count**: at ambient-cubic induced windows of
a vertex-disjoint family, the selected half-edges are covered by the candidate
germs up to their multiplicity and the high-degree loss. -/
theorem selected_le_candidates (family : Finset (Finset object.Vertex))
    (baseline : Graph.MinimumDegreeAtLeast 3 object)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    (large : 2 < object.vertexCount) {order : Nat}
    (induced : ∀ window ∈ family, object.InducesWindow order window)
    (disjoint : ∀ left ∈ family, ∀ right ∈ family, left ≠ right → Disjoint left right)
    (windowsCubic : ∀ w ∈ windowsOf object family, object.degree w = 3) :
    (3 * order - 2 * (order - 1) - 2) * family.card ≤
      3 * (stateBound S + 1) *
        (candidateGerms S 3 Target object family baseline bridgeless large).card +
        overlapBound 3 S * object.degreeSurplus 3 := by
  classical
  have perWindow : ∀ window ∈ family,
      3 * order - 2 * (order - 1) - 2 ≤ (externalStubList object window).length - 2 := by
    intro window windowMem
    have := stubCount_le_externalStubList_length object window (induced window windowMem)
      (fun vertex vertexMem => windowsCubic vertex
        ((mem_windowsOf object family vertex).2 ⟨window, windowMem, vertexMem⟩))
    omega
  have selectedCount : (3 * order - 2 * (order - 1) - 2) * family.card ≤
      (allSelectedStubs object family).card := by
    rw [card_allSelectedStubs object family disjoint]
    calc (3 * order - 2 * (order - 1) - 2) * family.card
        = ∑ _window ∈ family, (3 * order - 2 * (order - 1) - 2) := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ ∑ window ∈ family, ((externalStubList object window).length - 2) :=
          Finset.sum_le_sum perWindow
  refine selectedCount.trans ?_
  rw [← card_good_add_card_bad S 3 Target object family baseline bridgeless large]
  exact Nat.add_le_add (card_goodStubs_le S 3 Target object family baseline bridgeless large)
    (card_badStubs_le S Target object family baseline bridgeless large windowsCubic)

end Germ

end Hypostructure.Graph.ColdCorridor
