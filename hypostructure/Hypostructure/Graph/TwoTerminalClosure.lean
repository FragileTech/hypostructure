import Mathlib.Combinatorics.SimpleGraph.Sum
import Hypostructure.Graph.TightVertexSuppression
import Hypostructure.Graph.CutParity

/-! # The graph obtained by closing two two-terminal pieces -/

namespace Hypostructure.Graph.TwoTerminalClosure

open SimpleGraph

universe u

/-- In a simple path, an edge incident with the starting vertex is the first
edge.  This is the positional fact used to strip a distinguished closing edge
without choosing a list index. -/
theorem snd_eq_of_start_edge_mem {V : Type u} {G : SimpleGraph V}
    {start finish other : V} (walk : G.Walk start finish)
    (path : walk.IsPath) (member : s(start, other) ∈ walk.edges) :
    walk.snd = other := by
  induction walk with
  | nil => simp at member
  | @cons start next finish adjacent rest ih =>
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at member
      rcases member with first | later
      · rw [SimpleGraph.Walk.snd_cons]
        exact Sym2.congr_right.mp first.symm
      · have startInRest : start ∈ rest.support :=
          rest.fst_mem_support_of_mem_edges later
        exact ((SimpleGraph.Walk.cons_isPath_iff adjacent rest).mp path).2
          startInRest |>.elim

/-- Dual endpoint form of `snd_eq_of_start_edge_mem`. -/
theorem penultimate_eq_of_end_edge_mem {V : Type u} {G : SimpleGraph V}
    {start finish other : V} (walk : G.Walk start finish)
    (path : walk.IsPath) (member : s(finish, other) ∈ walk.edges) :
    walk.penultimate = other := by
  have reverseMember : s(finish, other) ∈ walk.reverse.edges := by
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]
    exact member
  have := snd_eq_of_start_edge_mem walk.reverse path.reverse reverseMember
  simpa using this

abbrev disjointSum (left right : FiniteObject.{u}) : FiniteObject.{u} where
  Vertex := left.Vertex ⊕ right.Vertex
  graph := left.graph ⊕g right.graph
  vertices := by
    letI : FinEnum left.Vertex := left.vertices
    letI : FinEnum right.Vertex := right.vertices
    infer_instance
  decideAdj := by
    intro x y
    cases x <;> cases y
    · exact left.decideAdj _ _
    · exact isFalse (by simp)
    · exact isFalse (by simp)
    · exact right.decideAdj _ _

abbrev close (left right : FiniteObject.{u})
    (a b : left.Vertex) (c d : right.Vertex) : FiniteObject.{u} :=
  ((disjointSum left right).addEdge (.inl a) (.inr c)).addEdge (.inl b) (.inr d)

@[simp] theorem close_adj (left right : FiniteObject.{u})
    (a b : left.Vertex) (c d : right.Vertex) (x y : left.Vertex ⊕ right.Vertex) :
    (close left right a b c d).graph.Adj x y ↔
      (left.graph ⊕g right.graph).Adj x y ∨
      ((x = .inl a ∧ y = .inr c) ∨ (x = .inr c ∧ y = .inl a)) ∨
      ((x = .inl b ∧ y = .inr d) ∨ (x = .inr d ∧ y = .inl b)) := by
  change ((((left.graph ⊕g right.graph) ⊔ edge (.inl a) (.inr c)) ⊔
    edge (.inl b) (.inr d)).Adj x y) ↔ _
  rw [SimpleGraph.sup_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj,
    SimpleGraph.edge_adj]
  aesop

/-- The closure has exactly two possible cut-crossing edges. -/
theorem crossing_edge_eq_first_or_second
    (left right : FiniteObject.{u}) (a b : left.Vertex) (c d : right.Vertex)
    [DecidablePred fun x => x ∈ Set.range (Sum.inl : left.Vertex → left.Vertex ⊕ right.Vertex)]
    (dart : (close left right a b c d).graph.Dart)
    (crossing : CutParity.crosses (Set.range Sum.inl) dart = true) :
    dart.edge = s((.inl a : left.Vertex ⊕ right.Vertex), .inr c) ∨
      dart.edge = s((.inl b : left.Vertex ⊕ right.Vertex), .inr d) := by
  rcases dart with ⟨⟨x, y⟩, adjacent⟩
  rcases x with x | x <;> rcases y with y | y
  · simp [CutParity.crosses, CutParity.side] at crossing
  · rcases (close_adj left right a b c d (.inl x) (.inr y)).mp adjacent with
      old | first | second
    · simp at old
    · left
      rcases first with first | first <;> simp at first ⊢
      exact ⟨first.1, first.2⟩
    · right
      rcases second with second | second <;> simp at second ⊢
      exact ⟨second.1, second.2⟩
  · rcases (close_adj left right a b c d (.inr x) (.inl y)).mp adjacent with
      old | first | second
    · simp at old
    · left
      rcases first with first | first <;> simp at first ⊢
      exact ⟨first.1, first.2⟩
    · right
      rcases second with second | second <;> simp at second ⊢
      exact ⟨second.1, second.2⟩
  · simp [CutParity.crosses, CutParity.side] at crossing

theorem closing_edges_mem_of_two_crossings
    (left right : FiniteObject.{u}) (a b : left.Vertex) (c d : right.Vertex)
    (hab : a ≠ b) (hcd : c ≠ d)
    [DecidablePred fun x => x ∈ Set.range (Sum.inl : left.Vertex → left.Vertex ⊕ right.Vertex)]
    {start : left.Vertex ⊕ right.Vertex}
    (cycle : (close left right a b c d).graph.Walk start start)
    (isCycle : cycle.IsCycle)
    (two : CutParity.crossings (Set.range Sum.inl) cycle = 2) :
    s((.inl a : left.Vertex ⊕ right.Vertex), .inr c) ∈ cycle.edges ∧
      s((.inl b : left.Vertex ⊕ right.Vertex), .inr d) ∈ cycle.edges := by
  classical
  let first := s((.inl a : left.Vertex ⊕ right.Vertex), .inr c)
  let second := s((.inl b : left.Vertex ⊕ right.Vertex), .inr d)
  let crossings := CutParity.crossingEdges (Set.range Sum.inl) cycle
  have edgeNe : first ≠ second := by
    intro equal
    rw [Sym2.eq_iff] at equal
    rcases equal with direct | reversed
    · exact hab (Sum.inl_injective direct.1)
    · exact Sum.inl_ne_inr reversed.1
  have classified : ∀ edge ∈ crossings, edge = first ∨ edge = second := by
    intro edge member
    rcases List.mem_map.mp member with ⟨dart, dartMember, rfl⟩
    have crossing : CutParity.crosses (Set.range Sum.inl) dart = true :=
      List.mem_filter.mp dartMember |>.2
    simpa [first, second] using
      crossing_edge_eq_first_or_second left right a b c d dart crossing
  have subset : crossings.toFinset ⊆ {first, second} := by
    intro edge member
    rcases classified edge (List.mem_toFinset.mp member) with rfl | rfl <;> simp
  have crossingsCard : crossings.toFinset.card = 2 := by
    rw [List.toFinset_card_of_nodup
      (CutParity.crossingEdges_nodup (Set.range Sum.inl) isCycle.isTrail),
      CutParity.length_crossingEdges, two]
  have pairCard : ({first, second} : Finset (Sym2 (left.Vertex ⊕ right.Vertex))).card = 2 := by
    simp [edgeNe]
  have equal : crossings.toFinset = {first, second} :=
    Finset.eq_of_subset_of_card_le subset (by omega)
  have firstCross : first ∈ crossings := by
    apply List.mem_toFinset.mp
    rw [equal]
    simp
  have secondCross : second ∈ crossings := by
    apply List.mem_toFinset.mp
    rw [equal]
    simp
  constructor
  · rcases List.mem_map.mp firstCross with ⟨dart, dartMember, dartEdge⟩
    have dartIn : dart ∈ cycle.darts := (List.mem_filter.mp dartMember).1
    change first ∈ cycle.edges
    rw [← dartEdge]
    exact List.mem_map.mpr ⟨dart, dartIn, rfl⟩
  · rcases List.mem_map.mp secondCross with ⟨dart, dartMember, dartEdge⟩
    have dartIn : dart ∈ cycle.darts := (List.mem_filter.mp dartMember).1
    change second ∈ cycle.edges
    rw [← dartEdge]
    exact List.mem_map.mpr ⟨dart, dartIn, rfl⟩

theorem crossings_le_two
    (left right : FiniteObject.{u}) (a b : left.Vertex) (c d : right.Vertex)
    [DecidablePred fun x => x ∈ Set.range (Sum.inl : left.Vertex → left.Vertex ⊕ right.Vertex)]
    {start : left.Vertex ⊕ right.Vertex}
    (cycle : (close left right a b c d).graph.Walk start start)
    (isCycle : cycle.IsCycle) :
    CutParity.crossings (Set.range Sum.inl) cycle ≤ 2 := by
  classical
  let crossings := CutParity.crossingEdges (Set.range Sum.inl) cycle
  have subset : crossings.toFinset ⊆
      {s((.inl a : left.Vertex ⊕ right.Vertex), .inr c),
       s((.inl b : left.Vertex ⊕ right.Vertex), .inr d)} := by
    intro edge member
    rcases List.mem_map.mp (List.mem_toFinset.mp member) with ⟨dart, dartMember, rfl⟩
    have classified := crossing_edge_eq_first_or_second left right a b c d dart
      (List.mem_filter.mp dartMember).2
    rcases classified with first | second
    · simp [first]
    · simp [second]
  rw [← CutParity.length_crossingEdges]
  change crossings.length ≤ 2
  rw [← List.toFinset_card_of_nodup
    (CutParity.crossingEdges_nodup (Set.range Sum.inl) isCycle.isTrail)]
  exact (Finset.card_le_card subset).trans Finset.card_le_two

@[simp] theorem vertexCount_close (left right : FiniteObject.{u})
    (a b : left.Vertex) (c d : right.Vertex) :
    (close left right a b c d).vertexCount = left.vertexCount + right.vertexCount := by
  letI : FinEnum left.Vertex := left.vertices
  letI : FinEnum right.Vertex := right.vertices
  let standard : FinEnum (left.Vertex ⊕ right.Vertex) := inferInstance
  change (disjointSum left right).vertices.card = left.vertices.card + right.vertices.card
  rw [FinEnum.card_unique (disjointSum left right).vertices standard]
  change standard.card = left.vertices.card + right.vertices.card
  simp [standard, FinEnum.card_eq_fintypeCard, Fintype.card_sum]

/-- A walk in the closure which stays in the left summand lifts, with its
length unchanged, to a walk in the left graph. -/
theorem exists_left_walk
    {left right : FiniteObject.{u}} {a b : left.Vertex} {c d : right.Vertex}
    {start finish : left.Vertex ⊕ right.Vertex} {x y : left.Vertex}
    (walk : (close left right a b c d).graph.Walk start finish)
    (startEq : start = .inl x) (finishEq : finish = .inl y)
    (inside : ∀ vertex ∈ walk.support, ∃ z : left.Vertex, vertex = .inl z) :
    ∃ lifted : left.graph.Walk x y, lifted.length = walk.length ∧
      walk.support = lifted.support.map Sum.inl := by
  induction walk generalizing x y with
  | nil =>
      have : x = y := Sum.inl_injective (startEq.symm.trans finishEq)
      subst y
      exact ⟨.nil, rfl, by simpa using startEq⟩
  | @cons start next finish adjacent rest ih =>
      obtain ⟨start', startForm⟩ := inside start (by simp)
      obtain ⟨next', nextForm⟩ := inside next (by simp)
      have startValue : start' = x :=
        Sum.inl_injective (startForm.symm.trans startEq)
      subst start'
      cases startForm
      cases nextForm
      have finishEq' : finish = .inl y := finishEq
      have oldAdj : left.graph.Adj x next' := by
        rcases (close_adj left right a b c d (.inl x) (.inl next')).mp adjacent with
          old | first | second
        · simpa using old
        · simp at first
        · simp at second
      have restInside : ∀ vertex ∈ rest.support,
          ∃ z : left.Vertex, vertex = .inl z := by
        intro vertex member
        exact inside vertex (by simp [member])
      obtain ⟨lifted, lengthEq, supportEq⟩ := ih rfl finishEq' restInside
      exact ⟨.cons oldAdj lifted, by simp [lengthEq], by simp [supportEq]⟩

/-- The symmetric lifting result for the right summand. -/
theorem exists_right_walk
    {left right : FiniteObject.{u}} {a b : left.Vertex} {c d : right.Vertex}
    {start finish : left.Vertex ⊕ right.Vertex} {x y : right.Vertex}
    (walk : (close left right a b c d).graph.Walk start finish)
    (startEq : start = .inr x) (finishEq : finish = .inr y)
    (inside : ∀ vertex ∈ walk.support, ∃ z : right.Vertex, vertex = .inr z) :
    ∃ lifted : right.graph.Walk x y, lifted.length = walk.length ∧
      walk.support = lifted.support.map Sum.inr := by
  induction walk generalizing x y with
  | nil =>
      have : x = y := Sum.inr_injective (startEq.symm.trans finishEq)
      subst y
      exact ⟨.nil, rfl, by simpa using startEq⟩
  | @cons start next finish adjacent rest ih =>
      obtain ⟨start', startForm⟩ := inside start (by simp)
      obtain ⟨next', nextForm⟩ := inside next (by simp)
      have startValue : start' = x :=
        Sum.inr_injective (startForm.symm.trans startEq)
      subst start'
      cases startForm
      cases nextForm
      have finishEq' : finish = .inr y := finishEq
      have oldAdj : right.graph.Adj x next' := by
        rcases (close_adj left right a b c d (.inr x) (.inr next')).mp adjacent with
          old | first | second
        · simpa using old
        · simp at first
        · simp at second
      have restInside : ∀ vertex ∈ rest.support,
          ∃ z : right.Vertex, vertex = .inr z := by
        intro vertex member
        exact inside vertex (by simp [member])
      obtain ⟨lifted, lengthEq, supportEq⟩ := ih rfl finishEq' restInside
      exact ⟨.cons oldAdj lifted, by simp [lengthEq], by simp [supportEq]⟩

/-- A crossing-free closure cycle based in the left summand is an actual
cycle of that summand, with unchanged length. -/
theorem exists_left_cycle
    {left right : FiniteObject.{u}} {a b : left.Vertex} {c d : right.Vertex}
    {x : left.Vertex}
    (cycle : (close left right a b c d).graph.Walk (.inl x) (.inl x))
    (isCycle : cycle.IsCycle)
    (inside : ∀ vertex ∈ cycle.support, ∃ z : left.Vertex, vertex = .inl z) :
    ∃ lifted : left.graph.Walk x x,
      lifted.IsCycle ∧ lifted.length = cycle.length := by
  obtain ⟨lifted, lengthEq, supportEq⟩ :=
    exists_left_walk cycle rfl rfl inside
  have tailNodup : lifted.support.tail.Nodup := by
    have mapped : (lifted.support.map
        (Sum.inl : left.Vertex → left.Vertex ⊕ right.Vertex)).tail.Nodup := by
      rw [← supportEq]
      exact isCycle.support_nodup
    cases supportShape : lifted.support with
    | nil => simp [supportShape]
    | cons head tail =>
        simp [supportShape] at mapped ⊢
        exact mapped.of_map
  have lengthThree : 3 ≤ lifted.length := by
    rw [lengthEq]
    exact isCycle.three_le_length
  have liftedCycle : lifted.IsCycle := by
    cases lifted with
    | nil => simp at lengthThree
    | @cons start next finish adjacency rest =>
        have restPath : rest.IsPath := by
          apply SimpleGraph.Walk.IsPath.mk'
          simpa using tailNodup
        rw [SimpleGraph.Walk.cons_isCycle_iff]
        refine ⟨restPath, ?_⟩
        intro member
        have member' : s(next, x) ∈ rest.edges := by
          simpa only [Sym2.eq_swap] using member
        have one := restPath.length_eq_one_of_mem_edges member'
        simp [one] at lengthThree
  exact ⟨lifted, liftedCycle, lengthEq⟩

/-- Symmetric right-summand cycle lift. -/
theorem exists_right_cycle
    {left right : FiniteObject.{u}} {a b : left.Vertex} {c d : right.Vertex}
    {x : right.Vertex}
    (cycle : (close left right a b c d).graph.Walk (.inr x) (.inr x))
    (isCycle : cycle.IsCycle)
    (inside : ∀ vertex ∈ cycle.support, ∃ z : right.Vertex, vertex = .inr z) :
    ∃ lifted : right.graph.Walk x x,
      lifted.IsCycle ∧ lifted.length = cycle.length := by
  obtain ⟨lifted, lengthEq, supportEq⟩ :=
    exists_right_walk cycle rfl rfl inside
  have tailNodup : lifted.support.tail.Nodup := by
    have mapped : (lifted.support.map
        (Sum.inr : right.Vertex → left.Vertex ⊕ right.Vertex)).tail.Nodup := by
      rw [← supportEq]
      exact isCycle.support_nodup
    cases supportShape : lifted.support with
    | nil => simp [supportShape]
    | cons head tail =>
        simp [supportShape] at mapped ⊢
        exact mapped.of_map
  have lengthThree : 3 ≤ lifted.length := by
    rw [lengthEq]
    exact isCycle.three_le_length
  have liftedCycle : lifted.IsCycle := by
    cases lifted with
    | nil => simp at lengthThree
    | @cons start next finish adjacency rest =>
        have restPath : rest.IsPath := by
          apply SimpleGraph.Walk.IsPath.mk'
          simpa using tailNodup
        rw [SimpleGraph.Walk.cons_isCycle_iff]
        refine ⟨restPath, ?_⟩
        intro member
        have member' : s(next, x) ∈ rest.edges := by
          simpa only [Sym2.eq_swap] using member
        have one := restPath.length_eq_one_of_mem_edges member'
        simp [one] at lengthThree
  exact ⟨lifted, liftedCycle, lengthEq⟩

theorem exists_left_path
    {left right : FiniteObject.{u}} {a b : left.Vertex} {c d : right.Vertex}
    {start finish : left.Vertex ⊕ right.Vertex} {x y : left.Vertex}
    (walk : (close left right a b c d).graph.Walk start finish)
    (startEq : start = .inl x) (finishEq : finish = .inl y)
    (path : walk.IsPath)
    (inside : ∀ vertex ∈ walk.support, ∃ z : left.Vertex, vertex = .inl z) :
    ∃ lifted : left.graph.Walk x y,
      lifted.IsPath ∧ lifted.length = walk.length := by
  obtain ⟨lifted, lengthEq, supportEq⟩ :=
    exists_left_walk walk startEq finishEq inside
  refine ⟨lifted, ?_, lengthEq⟩
  rw [SimpleGraph.Walk.isPath_def] at path ⊢
  rw [supportEq] at path
  exact path.of_map

theorem exists_right_path
    {left right : FiniteObject.{u}} {a b : left.Vertex} {c d : right.Vertex}
    {start finish : left.Vertex ⊕ right.Vertex} {x y : right.Vertex}
    (walk : (close left right a b c d).graph.Walk start finish)
    (startEq : start = .inr x) (finishEq : finish = .inr y)
    (path : walk.IsPath)
    (inside : ∀ vertex ∈ walk.support, ∃ z : right.Vertex, vertex = .inr z) :
    ∃ lifted : right.graph.Walk x y,
      lifted.IsPath ∧ lifted.length = walk.length := by
  obtain ⟨lifted, lengthEq, supportEq⟩ :=
    exists_right_walk walk startEq finishEq inside
  refine ⟨lifted, ?_, lengthEq⟩
  rw [SimpleGraph.Walk.isPath_def] at path ⊢
  rw [supportEq] at path
  exact path.of_map

theorem degree_disjoint_inl (left right : FiniteObject.{u}) (x : left.Vertex) :
    (disjointSum left right).degree (.inl x) = left.degree x := by
  rw [(disjointSum left right).degree_eq_ncard_neighborSet,
    left.degree_eq_ncard_neighborSet, SimpleGraph.neighborSet_sum_inl]
  exact Set.ncard_image_of_injective _ Sum.inl_injective

theorem degree_disjoint_inr (left right : FiniteObject.{u}) (x : right.Vertex) :
    (disjointSum left right).degree (.inr x) = right.degree x := by
  rw [(disjointSum left right).degree_eq_ncard_neighborSet,
    right.degree_eq_ncard_neighborSet, SimpleGraph.neighborSet_sum_inr]
  exact Set.ncard_image_of_injective _ Sum.inr_injective

theorem degree_left_first (left right : FiniteObject.{u})
    (a b : left.Vertex) (c d : right.Vertex) (hab : a ≠ b) :
    (close left right a b c d).degree (.inl a) = left.degree a + 1 := by
  rw [FiniteObject.degree_addEdge_of_ne,
    FiniteObject.degree_addEdge_left, degree_disjoint_inl]
  · simp
  · exact SimpleGraph.not_adj_sum_inl_inr _ _
  · exact fun h => hab (Sum.inl_injective h)
  · simp

theorem degree_right_first (left right : FiniteObject.{u})
    (a b : left.Vertex) (c d : right.Vertex) (hcd : c ≠ d) :
    (close left right a b c d).degree (.inr c) = right.degree c + 1 := by
  rw [FiniteObject.degree_addEdge_of_ne,
    FiniteObject.degree_addEdge_right, degree_disjoint_inr]
  · simp
  · exact SimpleGraph.not_adj_sum_inl_inr _ _
  · simp
  · exact fun h => hcd (Sum.inr_injective h)

theorem degree_left_second (left right : FiniteObject.{u})
    (a b : left.Vertex) (c d : right.Vertex) (hab : a ≠ b) :
    (close left right a b c d).degree (.inl b) = left.degree b + 1 := by
  rw [FiniteObject.degree_addEdge_left, FiniteObject.degree_addEdge_of_ne,
    degree_disjoint_inl]
  · exact fun h => hab (Sum.inl_injective h).symm
  · simp
  · simp
  · rw [FiniteObject.addEdge_adj]
    simp only [SimpleGraph.sum_adj, Sum.inl_ne_inr, false_and,
      or_false, false_or, Sum.inl.injEq, Sum.inr.injEq]
    rintro ⟨⟨h, _⟩, _⟩
    exact hab h.symm

theorem degree_right_second (left right : FiniteObject.{u})
    (a b : left.Vertex) (c d : right.Vertex) (hcd : c ≠ d) :
    (close left right a b c d).degree (.inr d) = right.degree d + 1 := by
  rw [FiniteObject.degree_addEdge_right, FiniteObject.degree_addEdge_of_ne,
    degree_disjoint_inr]
  · simp
  · exact fun h => hcd (Sum.inr_injective h).symm
  · simp
  · rw [FiniteObject.addEdge_adj]
    simp only [SimpleGraph.sum_adj, Sum.inl_ne_inr, false_and,
      or_false, false_or, Sum.inl.injEq, Sum.inr.injEq]
    rintro ⟨⟨_, h⟩, _⟩
    exact hcd h.symm

theorem degree_left_other (left right : FiniteObject.{u})
    (a b : left.Vertex) (c d : right.Vertex) (x : left.Vertex)
    (hxa : x ≠ a) (hxb : x ≠ b) :
    (close left right a b c d).degree (.inl x) = left.degree x := by
  rw [FiniteObject.degree_addEdge_of_ne, FiniteObject.degree_addEdge_of_ne,
    degree_disjoint_inl]
  · exact fun h => hxa (Sum.inl_injective h)
  · simp
  · exact fun h => hxb (Sum.inl_injective h)
  · simp

theorem degree_right_other (left right : FiniteObject.{u})
    (a b : left.Vertex) (c d : right.Vertex) (x : right.Vertex)
    (hxc : x ≠ c) (hxd : x ≠ d) :
    (close left right a b c d).degree (.inr x) = right.degree x := by
  rw [FiniteObject.degree_addEdge_of_ne, FiniteObject.degree_addEdge_of_ne,
    degree_disjoint_inr]
  · simp
  · exact fun h => hxc (Sum.inr_injective h)
  · simp
  · exact fun h => hxd (Sum.inr_injective h)

/-- A simple arc with no cut crossing lies wholly in the left summand and
therefore lifts without changing its length. -/
theorem left_path_of_noncrossing_arc
    (left right : FiniteObject.{u}) (a b : left.Vertex) (c d : right.Vertex)
    {start finish : left.Vertex}
    [DecidablePred fun x => x ∈ Set.range (Sum.inl : left.Vertex → left.Vertex ⊕ right.Vertex)]
    (arc : (close left right a b c d).graph.Walk (.inl start) (.inl finish))
    (path : arc.IsPath)
    (noCrossings : CutParity.crossings (Set.range Sum.inl) arc = 0) :
    ∃ lifted : left.graph.Walk start finish,
      lifted.IsPath ∧ lifted.length = arc.length := by
  have inside : ∀ vertex ∈ arc.support,
      ∃ z : left.Vertex, vertex = .inl z := by
    intro vertex member
    have sameSide := CutParity.side_of_crossings_eq_zero
      (Set.range Sum.inl) arc noCrossings vertex member
    rcases vertex with vertex | vertex
    · exact ⟨vertex, rfl⟩
    · simp [CutParity.side] at sameSide
  exact exists_left_path arc rfl rfl path inside

/-- After deleting the two closing edges from a simple crossing arc, its
interior is exactly a path in the right-hand summand. -/
theorem right_path_of_crossing_arc
    (left right : FiniteObject.{u}) (a b : left.Vertex) (c d : right.Vertex)
    {startLeft finishLeft : left.Vertex} {startRight finishRight : right.Vertex}
    [DecidablePred fun x => x ∈ Set.range (Sum.inl : left.Vertex → left.Vertex ⊕ right.Vertex)]
    (arc : (close left right a b c d).graph.Walk (.inl startLeft) (.inl finishLeft))
    (path : arc.IsPath)
    (firstEdge : s((.inl startLeft : left.Vertex ⊕ right.Vertex), .inr startRight) ∈ arc.edges)
    (lastEdge : s((.inl finishLeft : left.Vertex ⊕ right.Vertex), .inr finishRight) ∈ arc.edges)
    (exactCrossings : CutParity.crossings (Set.range Sum.inl) arc = 2) :
    ∃ middle : right.graph.Walk startRight finishRight,
      middle.IsPath ∧ middle.length + 2 = arc.length := by
  let cut : Set (left.Vertex ⊕ right.Vertex) := Set.range Sum.inl
  have sndEq := snd_eq_of_start_edge_mem arc path firstEdge
  have penultimateEq := penultimate_eq_of_end_edge_mem arc path lastEdge
  have arcNotNil : ¬ arc.Nil := by
    intro nil
    have noEdges := arc.edges_eq_nil.mpr nil
    rw [noEdges] at firstEdge
    simpa using firstEdge
  have tailCrossings : CutParity.crossings cut arc.tail = 1 := by
    have identity := CutParity.crossings_tail_add_first cut arc arcNotNil
    have crossing : CutParity.side cut (.inl startLeft) ≠
        CutParity.side cut arc.snd := by
      rw [sndEq]
      simp [cut, CutParity.side]
    simp only [crossing, ↓reduceIte] at identity
    change CutParity.crossings cut arc = 2 at exactCrossings
    omega
  have tailNotNil : ¬ arc.tail.Nil := by
    intro nil
    have : CutParity.crossings cut arc.tail = 0 := by rw [CutParity.crossings, arc.tail.darts_eq_nil.mpr nil]; rfl
    omega
  have tailPenultimateEq : arc.tail.penultimate = (.inr finishRight : left.Vertex ⊕ right.Vertex) := by
    rw [← arc.cons_tail_eq arcNotNil] at penultimateEq
    rw [SimpleGraph.Walk.penultimate_cons_of_not_nil
      (arc.adj_snd arcNotNil) arc.tail tailNotNil] at penultimateEq
    exact penultimateEq
  let interior := arc.tail.dropLast
  have interiorCrossings : CutParity.crossings cut interior = 0 := by
    have identity := CutParity.crossings_dropLast_add_last cut arc.tail tailNotNil
    have crossing : CutParity.side cut arc.tail.penultimate ≠
        CutParity.side cut (.inl finishLeft) := by
      rw [tailPenultimateEq]
      simp [cut, CutParity.side]
    simp only [crossing, ↓reduceIte] at identity
    change CutParity.crossings cut interior + 1 =
      CutParity.crossings cut arc.tail at identity
    omega
  have interiorPath : interior.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_dropLast tailNotNil]
    exact path.tail.support_nodup.sublist (List.dropLast_sublist _)
  have interiorInside : ∀ vertex ∈ interior.support,
      ∃ z : right.Vertex, vertex = .inr z := by
    intro vertex member
    have sameSide := CutParity.side_of_crossings_eq_zero cut interior
      interiorCrossings vertex member
    rcases vertex with vertex | vertex
    · simp [cut, CutParity.side, sndEq] at sameSide
    · exact ⟨vertex, rfl⟩
  obtain ⟨middle, middlePath, lengthEq⟩ :=
    exists_right_path interior sndEq tailPenultimateEq
      interiorPath interiorInside
  refine ⟨middle, middlePath, ?_⟩
  dsimp [interior] at lengthEq ⊢
  rw [lengthEq]
  have firstLength := arc.length_tail_add_one arcNotNil
  have lastLength := arc.tail.length_dropLast_add_one tailNotNil
  omega

/-- Exact two-path output from a partitioned cycle. -/
theorem paths_of_partitioned_cycle
    (left right : FiniteObject.{u}) (a b : left.Vertex) (c d : right.Vertex)
    {startLeft finishLeft : left.Vertex} {startRight finishRight : right.Vertex}
    [DecidablePred fun x => x ∈ Set.range (Sum.inl : left.Vertex → left.Vertex ⊕ right.Vertex)]
    (leftArc rightArc :
      (close left right a b c d).graph.Walk (.inl startLeft) (.inl finishLeft))
    (leftPath : leftArc.IsPath) (rightPath : rightArc.IsPath)
    (leftNone : CutParity.crossings (Set.range Sum.inl) leftArc = 0)
    (firstEdge : s((.inl startLeft : left.Vertex ⊕ right.Vertex), .inr startRight) ∈ rightArc.edges)
    (lastEdge : s((.inl finishLeft : left.Vertex ⊕ right.Vertex), .inr finishRight) ∈ rightArc.edges)
    (rightTwo : CutParity.crossings (Set.range Sum.inl) rightArc = 2)
    {cycleLength : Nat}
    (partitionLength : leftArc.length + rightArc.length = cycleLength) :
    ∃ leftMiddle : left.graph.Walk startLeft finishLeft,
      ∃ rightMiddle : right.graph.Walk startRight finishRight,
        leftMiddle.IsPath ∧ rightMiddle.IsPath ∧
          leftMiddle.length + rightMiddle.length + 2 = cycleLength := by
  obtain ⟨leftMiddle, leftMiddlePath, leftLength⟩ :=
    left_path_of_noncrossing_arc left right a b c d leftArc leftPath leftNone
  obtain ⟨rightMiddle, rightMiddlePath, rightLength⟩ :=
    right_path_of_crossing_arc left right a b c d rightArc rightPath
      firstEdge lastEdge rightTwo
  exact ⟨leftMiddle, rightMiddle, leftMiddlePath, rightMiddlePath, by omega⟩

/-- Rotate and, if necessary, reverse a closure cycle so that its first dart
is the selected first closing edge. -/
theorem exists_rooted_cycle
    (left right : FiniteObject.{u}) (a b : left.Vertex) (c d : right.Vertex)
    {start : left.Vertex ⊕ right.Vertex}
    (cycle : (close left right a b c d).graph.Walk start start)
    (isCycle : cycle.IsCycle)
    (usesFirst : s((.inl a : left.Vertex ⊕ right.Vertex), .inr c) ∈
      cycle.edges) :
    ∃ rooted : (close left right a b c d).graph.Walk (.inl a) (.inl a),
      rooted.IsCycle ∧ rooted.length = cycle.length ∧
        rooted.snd = .inr c := by
  letI : DecidableEq (left.Vertex ⊕ right.Vertex) :=
    (close left right a b c d).vertices.decEq
  exact CutParity.exists_oriented_cycle_of_edge
    (G := (close left right a b c d).graph)
    (Sum.inl_ne_inr : (.inl a : left.Vertex ⊕ right.Vertex) ≠ .inr c)
    cycle isCycle usesFirst

/-- The exact rooted partition data of a closure cycle.  It is a
mathematical object, not an auxiliary proof-data interface. -/
structure RootedCyclePartition
    (left right : FiniteObject.{u}) (a b : left.Vertex) (c d : right.Vertex)
    (cycleLength : Nat)
    [DecidablePred fun x => x ∈ Set.range (Sum.inl : left.Vertex → left.Vertex ⊕ right.Vertex)] where
  startLeft : left.Vertex
  finishLeft : left.Vertex
  startRight : right.Vertex
  finishRight : right.Vertex
  leftArc : (close left right a b c d).graph.Walk
    (.inl startLeft) (.inl finishLeft)
  rightArc : (close left right a b c d).graph.Walk
    (.inl startLeft) (.inl finishLeft)
  leftPath : leftArc.IsPath
  rightPath : rightArc.IsPath
  leftNone : CutParity.crossings (Set.range Sum.inl) leftArc = 0
  firstEdge : s((.inl startLeft : left.Vertex ⊕ right.Vertex),
    .inr startRight) ∈ rightArc.edges
  lastEdge : s((.inl finishLeft : left.Vertex ⊕ right.Vertex),
    .inr finishRight) ∈ rightArc.edges
  rightTwo : CutParity.crossings (Set.range Sum.inl) rightArc = 2
  partitionLength : leftArc.length + rightArc.length = cycleLength

set_option maxHeartbeats 800000 in
noncomputable def rootedPartition_of_two_crossings
    (left right : FiniteObject.{u}) (a b : left.Vertex) (c d : right.Vertex)
    (hab : a ≠ b) (hcd : c ≠ d)
    [DecidablePred fun x => x ∈ Set.range (Sum.inl : left.Vertex → left.Vertex ⊕ right.Vertex)]
    (rooted : (close left right a b c d).graph.Walk (.inl a) (.inl a))
    (isCycle : rooted.IsCycle)
    (firstSnd : rooted.snd = .inr c)
    (two : CutParity.crossings (Set.range Sum.inl) rooted = 2) :
    RootedCyclePartition left right a b c d rooted.length := by
  classical
  have edges := closing_edges_mem_of_two_crossings left right a b c d
    hab hcd rooted isCycle two
  have bMem : (.inl b : left.Vertex ⊕ right.Vertex) ∈ rooted.support :=
    rooted.fst_mem_support_of_mem_edges edges.2
  let rightArc := rooted.takeUntil (.inl b) bMem
  let complement := rooted.dropUntil (.inl b) bMem
  let leftArc := complement.reverse
  have rightNotNil : ¬ rightArc.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (fun equality => hab (Sum.inl_injective equality))
  have rightSnd : rightArc.snd = (.inr c : left.Vertex ⊕ right.Vertex) := by
    dsimp [rightArc]
    rw [SimpleGraph.Walk.snd_takeUntil
      (fun equality => hab (Sum.inl_injective equality.symm))]
    exact firstSnd
  have cMem : (.inr c : left.Vertex ⊕ right.Vertex) ∈ rightArc.support := by
    rw [← rightSnd]
    exact List.mem_of_mem_tail (SimpleGraph.Walk.snd_mem_tail_support rightNotNil)
  have positive : 0 < CutParity.crossings (Set.range Sum.inl) rightArc := by
    apply CutParity.crossings_pos (Set.range Sum.inl) rightArc cMem
    simp [CutParity.side]
  have even := CutParity.crossings_mod_two (Set.range Sum.inl) rightArc
  have split := SimpleGraph.Walk.take_spec rooted bMem
  have split' : rightArc.append complement = rooted := by
    exact split
  have crossingSplit : CutParity.crossings (Set.range Sum.inl) rightArc +
      CutParity.crossings (Set.range Sum.inl) complement = 2 := by
    have add := CutParity.crossings_append (Set.range Sum.inl) rightArc complement
    have total : CutParity.crossings (Set.range Sum.inl)
        (rightArc.append complement) = 2 := by
      rw [split']
      exact two
    exact add.symm.trans total
  have rightTwo : CutParity.crossings (Set.range Sum.inl) rightArc = 2 := by
    have parity : CutParity.crossings (Set.range Sum.inl) rightArc % 2 = 0 := by
      simpa [CutParity.side] using even
    omega
  have complementNone : CutParity.crossings (Set.range Sum.inl) complement = 0 := by
    omega
  have crossingEdgesInRight :
      s((.inl a : left.Vertex ⊕ right.Vertex), .inr c) ∈ rightArc.edges ∧
      s((.inl b : left.Vertex ⊕ right.Vertex), .inr d) ∈ rightArc.edges := by
    have place (edge : Sym2 (left.Vertex ⊕ right.Vertex))
        (member : edge ∈ rooted.edges)
        (cross : edge = s((.inl a : left.Vertex ⊕ right.Vertex), .inr c) ∨
          edge = s((.inl b : left.Vertex ⊕ right.Vertex), .inr d)) :
        edge ∈ rightArc.edges := by
      rw [← split, SimpleGraph.Walk.edges_append, List.mem_append] at member
      rcases member with member | member
      · exact member
      · exfalso
        have oppositeMem : ∃ x : right.Vertex,
            (.inr x : left.Vertex ⊕ right.Vertex) ∈ complement.support := by
          rcases cross with rfl | rfl
          · exact ⟨c, complement.snd_mem_support_of_mem_edges member⟩
          · exact ⟨d, complement.snd_mem_support_of_mem_edges member⟩
        obtain ⟨x, xMem⟩ := oppositeMem
        have pos := CutParity.crossings_pos (Set.range Sum.inl) complement xMem (by
          simp [CutParity.side])
        omega
    exact ⟨place _ edges.1 (Or.inl rfl), place _ edges.2 (Or.inr rfl)⟩
  have rightPath : rightArc.IsPath := isCycle.isPath_takeUntil bMem
  have complementPath : complement.IsPath := by
    have appendedCycle : (rightArc.append complement).IsCycle := by
      rw [split']
      exact isCycle
    exact appendedCycle.isPath_of_append_right rightNotNil
  exact {
    startLeft := a
    finishLeft := b
    startRight := c
    finishRight := d
    leftArc := leftArc
    rightArc := rightArc
    leftPath := complementPath.reverse
    rightPath := rightPath
    leftNone := by
      dsimp [leftArc]
      rw [CutParity.crossings_reverse]
      exact complementNone
    firstEdge := crossingEdgesInRight.1
    lastEdge := crossingEdgesInRight.2
    rightTwo := rightTwo
    partitionLength := by
      dsimp [leftArc]
      rw [SimpleGraph.Walk.length_reverse]
      calc
        complement.length + rightArc.length = rightArc.length + complement.length :=
          Nat.add_comm _ _
        _ = (rightArc.append complement).length := by
          rw [SimpleGraph.Walk.length_append]
        _ = rooted.length := by rw [split']
  }

/-- Extract the two terminal paths directly from a rooted closure cycle with
exactly two cut crossings. -/
theorem paths_of_rooted_cycle
    (left right : FiniteObject.{u}) (a b : left.Vertex) (c d : right.Vertex)
    (hab : a ≠ b) (hcd : c ≠ d)
    [DecidablePred fun x => x ∈ Set.range (Sum.inl : left.Vertex → left.Vertex ⊕ right.Vertex)]
    (rooted : (close left right a b c d).graph.Walk (.inl a) (.inl a))
    (isCycle : rooted.IsCycle)
    (firstSnd : rooted.snd = .inr c)
    (two : CutParity.crossings (Set.range Sum.inl) rooted = 2) :
    ∃ leftMiddle : left.graph.Walk a b,
      ∃ rightMiddle : right.graph.Walk c d,
        leftMiddle.IsPath ∧ rightMiddle.IsPath ∧
          leftMiddle.length + rightMiddle.length + 2 = rooted.length := by
  let partition := rootedPartition_of_two_crossings left right a b c d
    hab hcd rooted isCycle firstSnd two
  exact paths_of_partitioned_cycle left right a b c d
    partition.leftArc partition.rightArc partition.leftPath partition.rightPath
    partition.leftNone partition.firstEdge partition.lastEdge partition.rightTwo
    partition.partitionLength

/-- Extract the two terminal paths from an arbitrarily based and oriented
closure cycle with exactly two cut crossings. -/
theorem paths_of_cycle
    (left right : FiniteObject.{u}) (a b : left.Vertex) (c d : right.Vertex)
    (hab : a ≠ b) (hcd : c ≠ d)
    [DecidablePred fun x => x ∈ Set.range (Sum.inl : left.Vertex → left.Vertex ⊕ right.Vertex)]
    {start : left.Vertex ⊕ right.Vertex}
    (cycle : (close left right a b c d).graph.Walk start start)
    (isCycle : cycle.IsCycle)
    (two : CutParity.crossings (Set.range Sum.inl) cycle = 2) :
    ∃ leftMiddle : left.graph.Walk a b,
      ∃ rightMiddle : right.graph.Walk c d,
        leftMiddle.IsPath ∧ rightMiddle.IsPath ∧
          leftMiddle.length + rightMiddle.length + 2 = cycle.length := by
  classical
  have closing := closing_edges_mem_of_two_crossings left right a b c d
    hab hcd cycle isCycle two
  obtain ⟨rooted, rootedCycle, rootedLength, rootedSnd, rootedCrossings⟩ :=
    CutParity.exists_oriented_cycle_of_edge_with_crossings
      (S := Set.range (Sum.inl : left.Vertex → left.Vertex ⊕ right.Vertex))
      (G := (close left right a b c d).graph)
      (Sum.inl_ne_inr : (.inl a : left.Vertex ⊕ right.Vertex) ≠ .inr c)
      cycle isCycle closing.1
  obtain ⟨leftMiddle, rightMiddle, leftPath, rightPath, lengthEq⟩ :=
    paths_of_rooted_cycle left right a b c d hab hcd rooted rootedCycle rootedSnd
      (rootedCrossings.trans two)
  exact ⟨leftMiddle, rightMiddle, leftPath, rightPath, by omega⟩

/-- Certificate form: once a closure certificate is known to cross the
summand cut, the closure's two-edge boundary and parity determine the complete
terminal-path decomposition internally. -/
theorem paths_of_cycleCertificate
    {LengthOK : Nat → Prop}
    (left right : FiniteObject.{u}) (a b : left.Vertex) (c d : right.Vertex)
    (hab : a ≠ b) (hcd : c ≠ d)
    [DecidablePred fun x => x ∈ Set.range (Sum.inl : left.Vertex → left.Vertex ⊕ right.Vertex)]
    (certificate : CycleCertificate (close left right a b c d) LengthOK)
    (positive : 0 < CutParity.crossings (Set.range Sum.inl) certificate.walk) :
    ∃ leftMiddle : left.graph.Walk a b,
      ∃ rightMiddle : right.graph.Walk c d,
        leftMiddle.IsPath ∧ rightMiddle.IsPath ∧
          leftMiddle.length + rightMiddle.length + 2 = certificate.walk.length := by
  have lower := CutParity.two_le_crossings (Set.range Sum.inl)
    certificate.walk positive
  have upper := crossings_le_two left right a b c d
    certificate.walk certificate.isCycle
  exact paths_of_cycle left right a b c d hab hcd certificate.walk
    certificate.isCycle (by omega)

/-- Avoidance in both summands forces every accepted closure certificate to
cross their cut. -/
theorem cycleCertificate_crossings_pos_of_avoids
    {LengthOK : Nat → Prop}
    (left right : FiniteObject.{u}) (a b : left.Vertex) (c d : right.Vertex)
    [DecidablePred fun x => x ∈ Set.range (Sum.inl : left.Vertex → left.Vertex ⊕ right.Vertex)]
    (leftAvoids : ¬ HasCycleWithLength LengthOK left)
    (rightAvoids : ¬ HasCycleWithLength LengthOK right)
    (certificate : CycleCertificate (close left right a b c d) LengthOK) :
    0 < CutParity.crossings (Set.range Sum.inl) certificate.walk := by
  rcases certificate with ⟨vertex, walk, isCycle, lengthOk⟩
  rcases vertex with x | x
  · by_contra notPositive
    have none : CutParity.crossings (Set.range Sum.inl) walk = 0 :=
      Nat.eq_zero_of_not_pos notPositive
    have inside : ∀ vertex ∈ walk.support,
        ∃ z : left.Vertex, vertex = .inl z := by
      intro vertex member
      have same := CutParity.side_of_crossings_eq_zero
        (Set.range Sum.inl) walk none vertex member
      rcases vertex with vertex | vertex
      · exact ⟨vertex, rfl⟩
      · simp [CutParity.side] at same
    obtain ⟨lifted, liftedCycle, lengthEq⟩ :=
      exists_left_cycle walk isCycle inside
    apply leftAvoids
    exact ⟨{
      vertex := x
      walk := lifted
      isCycle := liftedCycle
      length_ok := by rw [lengthEq]; exact lengthOk
    }⟩
  · by_contra notPositive
    have none : CutParity.crossings (Set.range Sum.inl) walk = 0 :=
      Nat.eq_zero_of_not_pos notPositive
    have inside : ∀ vertex ∈ walk.support,
        ∃ z : right.Vertex, vertex = .inr z := by
      intro vertex member
      have same := CutParity.side_of_crossings_eq_zero
        (Set.range Sum.inl) walk none vertex member
      rcases vertex with vertex | vertex
      · simp [CutParity.side] at same
      · exact ⟨vertex, rfl⟩
    obtain ⟨lifted, liftedCycle, lengthEq⟩ :=
      exists_right_cycle walk isCycle inside
    apply rightAvoids
    exact ⟨{
      vertex := x
      walk := lifted
      isCycle := liftedCycle
      length_ok := by rw [lengthEq]; exact lengthOk
    }⟩

/-- Fully unconditional certificate decomposition under the two avoidance
hypotheses used by minimal-counterexample closure arguments. -/
theorem paths_of_cycleCertificate_of_avoids
    {LengthOK : Nat → Prop}
    (left right : FiniteObject.{u}) (a b : left.Vertex) (c d : right.Vertex)
    (hab : a ≠ b) (hcd : c ≠ d)
    [DecidablePred fun x => x ∈ Set.range (Sum.inl : left.Vertex → left.Vertex ⊕ right.Vertex)]
    (leftAvoids : ¬ HasCycleWithLength LengthOK left)
    (rightAvoids : ¬ HasCycleWithLength LengthOK right)
    (certificate : CycleCertificate (close left right a b c d) LengthOK) :
    ∃ leftMiddle : left.graph.Walk a b,
      ∃ rightMiddle : right.graph.Walk c d,
        leftMiddle.IsPath ∧ rightMiddle.IsPath ∧
          leftMiddle.length + rightMiddle.length + 2 = certificate.walk.length := by
  exact paths_of_cycleCertificate left right a b c d hab hcd certificate
    (cycleCertificate_crossings_pos_of_avoids left right a b c d
      leftAvoids rightAvoids certificate)

/-- Minimality applied to a smaller two-terminal closure gives the exact pair
of terminal paths whose lengths, together with the two closing edges, have an
accepted total length. -/
theorem terminal_paths_of_minimal_closure
    {LengthOK : Nat → Prop}
    (ambient left right : FiniteObject.{u})
    (a b : left.Vertex) (c d : right.Vertex)
    (hab : a ≠ b) (hcd : c ≠ d)
    (leftAvoids : ¬ HasCycleWithLength LengthOK left)
    (rightAvoids : ¬ HasCycleWithLength LengthOK right)
    (smaller : (close left right a b c d).LexicographicallySmaller ambient)
    (baseline : 3 ≤ (close left right a b c d).minDegree)
    (minimal : ∀ candidate : FiniteObject.{u},
      candidate.LexicographicallySmaller ambient →
      3 ≤ candidate.minDegree → HasCycleWithLength LengthOK candidate) :
    ∃ leftMiddle : left.graph.Walk a b,
      ∃ rightMiddle : right.graph.Walk c d,
        leftMiddle.IsPath ∧ rightMiddle.IsPath ∧
          LengthOK (leftMiddle.length + rightMiddle.length + 2) := by
  classical
  obtain ⟨certificate⟩ := minimal _ smaller baseline
  obtain ⟨leftMiddle, rightMiddle, leftPath, rightPath, lengthEq⟩ :=
    paths_of_cycleCertificate_of_avoids left right a b c d hab hcd
      leftAvoids rightAvoids certificate
  exact ⟨leftMiddle, rightMiddle, leftPath, rightPath, by
    rw [lengthEq]
    exact certificate.length_ok⟩

end Hypostructure.Graph.TwoTerminalClosure
