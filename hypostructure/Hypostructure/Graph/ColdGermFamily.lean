import Hypostructure.Graph.ColdFirstFailure
import Hypostructure.Graph.SubcubicReach

/-!
# The (F5) cold bounded germs of the selected half-edges

`def:cold-corridor-first-failure` and `def:cold-bounded-germ`, constructed:

* the outside component `K` of a boundary stub's foot in `G − X_cold`;
* the first-failure exchange support of a corridor — the whole terminal
  corridor, or the bounded prefix inside which a cold corridor state repeats
  (`Q_cold + 1` initial segments) — as a connected proper support;
* the geometric support on which the ledger-retained cold bounded configuration
  is read.

This file deliberately does not construct a `BoundedGerm`.  The two
same-interface representatives and their exact retained record are semantic
witnesses of `K .coldCorridorState`; manufacturing a default record or replacing
the paper's exchange representative by the corridor piece would change the
proof.
-/

namespace Hypostructure.Graph.ColdCorridor

open Hypostructure

universe u

variable {object : FiniteObject.{u}}

/-- A graph whose registered minimum-degree threshold is at least three has
more than two vertices.  The threshold is supplied by the problem
presentation; this lemma does not specialize its caller to a literal cubic
baseline. -/
theorem two_lt_vertexCount_of_minDegree {threshold : Nat}
    (three_le : 3 ≤ threshold)
    (baseline : Graph.MinimumDegreeAtLeast threshold object) :
    2 < object.vertexCount := by
  classical
  by_cases nonempty : Nonempty object.Vertex
  · obtain ⟨vertex⟩ := nonempty
    have := object.minDegree_le_degree vertex
    have := object.degree_lt_vertexCount vertex
    change threshold ≤ object.minDegree at baseline
    omega
  · exfalso
    rw [not_nonempty_iff] at nonempty
    change threshold ≤ object.minDegree at baseline
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

/-! ## The selected branch-excess half-edges and their germs

`def:cold-skeleton-excess`: *"keep one incident half-edge for every edge of `G`
leaving `P` … the first two stubs of `P` are called the transit stubs; the
remaining `s(P)−2` stubs are the selected branch-excess half-edges of `P`."*
Only selected half-edges whose outside endpoint lies in the outside graph enter
the paper's cold-return construction.  No replacement object is assigned to a
half-edge that does not satisfy that hypothesis. -/

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

/-! ## Selected half-edges in the cold-window union -/

section Germ

variable (object : FiniteObject.{u})

/-- The foot of an outside stub lies in its own outside component. -/
theorem foot_mem_outsideComponentOf (windows : Finset object.Vertex)
    (foot : object.Vertex) (footOutside : foot ∉ windows) :
    foot ∈ outsideComponentOf object windows foot footOutside := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  simp only [outsideComponentOf, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨(mem_outsideSupport object windows foot).2 footOutside, SimpleGraph.Reachable.refl _⟩

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


/-!
The multiplicity, high-degree-loss, and overlap estimates belong to the actual
first-failure incidence published at node `[153]`.  This module does not
reconstruct that incidence from the ambient graph.
-/

end Germ

end Hypostructure.Graph.ColdCorridor
