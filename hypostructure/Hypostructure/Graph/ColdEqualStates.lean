import Hypostructure.Graph.GluedCycleSides
import Hypostructure.Graph.ColdGermFamily

/-!
# Equal cut states on a cold corridor, read inside G

Vocabulary-free library for node `[153]`'s equal-state pairs at G
(`lem:cold-corridor-first-failure`, tex 7187-7197, 7265-7270).

For a cold return corridor in an outside component, and two segments
`left < right`, the two readings of the pair are `retainedPiece J_right J_left`
and `retainedPiece J_right J_right` on the one boundary `∂J_right`:

* `prefix_profile_ne`: they have different boundary-degree profiles --
  `head right` is on `∂J_right` and loses its corridor edge to `head (right-1)`
  in the `J_left` reading;
* `first_lt_stateBound`: pairwise distinct states up to `first` force
  `first < Q_cold`.

Only G's own readings occur.  (The separating path context of the earlier
group-F2 analysis, an outside context that is not part of G, is not part of
this library.)
-/

namespace Hypostructure.Graph.ColdEqualStates

open Hypostructure Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe v

section Readings

variable {object : FiniteObject.{v}}

theorem pieceDecode_mem (Z : Finset object.Vertex)
    (w : (SupportAtom.boundary object Z).Vertex ⊕ SupportAtom.PieceInternal object Z) :
    SupportAtom.pieceDecode object Z w ∈ Z := by
  rcases w with b | i
  · exact ((SupportAtom.mem_cutBoundary_iff object Z b.1).1 b.2).1
  · exact i.2.1

/-- The piece-side vertex of a support vertex. -/
noncomputable def enc (Z : Finset object.Vertex) (w : object.Vertex) (hw : w ∈ Z) :
    (SupportAtom.boundary object Z).Vertex ⊕ SupportAtom.PieceInternal object Z := by
  classical
  exact if hb : w ∈ SupportAtom.cutBoundary object Z then .inl ⟨w, hb⟩
    else .inr ⟨w, hw, hb⟩

theorem pieceDecode_enc (Z : Finset object.Vertex) (w : object.Vertex) (hw : w ∈ Z) :
    SupportAtom.pieceDecode object Z (enc Z w hw) = w := by
  unfold enc
  split <;> rfl

theorem retained_adj_iff (Z L : Finset object.Vertex)
    (a b : (SupportAtom.boundary object Z).Vertex ⊕ SupportAtom.PieceInternal object Z) :
    (SupportAtom.retainedPiece object Z L).graph.Adj a b ↔
      object.graph.Adj (SupportAtom.pieceDecode object Z a)
          (SupportAtom.pieceDecode object Z b) ∧
        SupportAtom.pieceDecode object Z a ∈ L ∧
        SupportAtom.pieceDecode object Z b ∈ L := by
  simp only [SupportAtom.retainedPiece, SimpleGraph.inf_adj, SimpleGraph.comap_adj,
    SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨adj, _, (h | h)⟩
    · exact ⟨adj, h⟩
    · exact ⟨adj, h.2, h.1⟩
  · rintro ⟨adj, ha, hb⟩
    exact ⟨adj, adj.ne, Or.inl ⟨ha, hb⟩⟩

/-- **A boundary vertex that loses an edge lowers its `d_∂` entry.**  If the
cut-boundary vertex `b` of `Z` has a `G`-neighbour `w ∈ Z` and the edge `bw`
is not retained by `L`, then `b`'s degree in `retainedPiece Z L` is strictly
below its degree in the full reading `retainedPiece Z Z`. -/
theorem retained_boundaryDegree_lt (Z L : Finset object.Vertex)
    (b : object.Vertex) (hb : b ∈ SupportAtom.cutBoundary object Z)
    (w : object.Vertex) (hw : w ∈ Z) (adj : object.graph.Adj b w)
    (lost : b ∉ L ∨ w ∉ L) :
    (SupportAtom.retainedPiece object Z L).boundaryDegree ⟨b, hb⟩ <
      (SupportAtom.retainedPiece object Z Z).boundaryDegree ⟨b, hb⟩ := by
  classical
  unfold BoundaryPiece.boundaryDegree
  rw [FiniteObject.degree_eq_ncard_neighborSet,
    FiniteObject.degree_eq_ncard_neighborSet]
  have finite : Set.Finite ((SupportAtom.retainedPiece object Z Z).pack.graph.neighborSet
      (.inl ⟨b, hb⟩)) :=
    @Set.toFinite _ _ (@Subtype.finite _
      (@Finite.of_fintype _
        (@FinEnum.instFintype _ (SupportAtom.retainedPiece object Z Z).pack.vertices)) _)
  apply Set.ncard_lt_ncard _ finite
  refine ⟨fun x hx => ?_, fun sub => ?_⟩
  · change (SupportAtom.retainedPiece object Z L).graph.Adj _ _ at hx
    change (SupportAtom.retainedPiece object Z Z).graph.Adj _ _
    rw [retained_adj_iff] at hx ⊢
    exact ⟨hx.1, pieceDecode_mem Z _, pieceDecode_mem Z _⟩
  · have inZ : enc Z w hw ∈
        (SupportAtom.retainedPiece object Z Z).pack.graph.neighborSet (.inl ⟨b, hb⟩) := by
      change (SupportAtom.retainedPiece object Z Z).graph.Adj _ _
      rw [retained_adj_iff, pieceDecode_enc]
      exact ⟨adj, pieceDecode_mem Z _, hw⟩
    have inL := sub inZ
    change (SupportAtom.retainedPiece object Z L).graph.Adj _ _ at inL
    rw [retained_adj_iff, pieceDecode_enc] at inL
    rcases lost with lost | lost
    · exact lost inL.2.1
    · exact lost inL.2.2

/-- **Profile equality forces a closed, edge-preserving boundary.**  If the
readings `retainedPiece Z L` and `retainedPiece Z Z` have the same `d_∂`, then
no cut-boundary vertex of `Z` loses an edge: every boundary vertex lies in `L`
and every edge from it into `Z` ends in `L`. -/
theorem retained_profile_eq_imp (Z L : Finset object.Vertex)
    (same : (SupportAtom.retainedPiece object Z L).boundaryDegreeProfile =
      (SupportAtom.retainedPiece object Z Z).boundaryDegreeProfile) :
    ∀ b ∈ SupportAtom.cutBoundary object Z, ∀ w ∈ Z,
      object.graph.Adj b w → b ∈ L ∧ w ∈ L := by
  intro b hb w hw adj
  by_contra lost
  have lt := retained_boundaryDegree_lt Z L b hb w hw adj (by tauto)
  have eq := congrFun same ⟨b, hb⟩
  unfold BoundaryPiece.boundaryDegreeProfile at eq
  omega

end Readings

/-! ### Corridor facts -/

section Corridor

variable {object : FiniteObject.{v}} {windows component : Finset object.Vertex}

theorem head_mem_prefixSupport_iff
    (corridor : ColdCorridor.Corridor object windows component)
    (s : corridor.Segment) (n : Nat) :
    corridor.head s ∈ corridor.prefixSupport n ↔ s.1 ≤ n := by
  classical
  constructor
  · intro mem
    obtain ⟨inner, innerMem, innerEq⟩ := (corridor.mem_prefixSupport n _).1 mem
    obtain ⟨i, hi, hiLe⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp innerMem
    rw [SimpleGraph.Walk.take_getVert] at hi
    have takeLen := SimpleGraph.Walk.take_length corridor.inside.1 n
    have eq : corridor.inside.1.getVert (min n i) = corridor.inside.1.getVert s.1 := by
      apply Subtype.ext
      rw [hi]
      exact innerEq
    have inj := corridor.inside.2.getVert_injOn
      (show min n i ∈ {j | j ≤ corridor.inside.1.length} by
        simp only [Set.mem_setOf_eq]; omega)
      (show s.1 ∈ {j | j ≤ corridor.inside.1.length} by
        simp only [Set.mem_setOf_eq]; omega) eq
    omega
  · intro le
    refine (corridor.mem_prefixSupport n _).2
      ⟨(corridor.inside.1.take n).getVert s.1, ?_, ?_⟩
    · exact SimpleGraph.Walk.getVert_mem_support _ _
    · rw [SimpleGraph.Walk.take_getVert, Nat.min_eq_right le]
      rfl

/-- Every vertex of a prefix is the head of a segment inside it. -/
theorem mem_prefixSupport_iff_head
    (corridor : ColdCorridor.Corridor object windows component) (n : Nat)
    (vertex : object.Vertex) :
    vertex ∈ corridor.prefixSupport n ↔
      ∃ s : corridor.Segment, s.1 ≤ n ∧ corridor.head s = vertex := by
  constructor
  · intro mem
    obtain ⟨inner, innerMem, innerEq⟩ := (corridor.mem_prefixSupport n _).1 mem
    obtain ⟨i, hi, hiLe⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp innerMem
    rw [SimpleGraph.Walk.take_getVert] at hi
    have takeLen := SimpleGraph.Walk.take_length corridor.inside.1 n
    refine ⟨⟨min n i, by omega⟩, Nat.min_le_left _ _, ?_⟩
    change (corridor.inside.1.getVert (min n i)).1 = vertex
    rw [hi]
    exact innerEq
  · rintro ⟨s, le, rfl⟩
    exact (head_mem_prefixSupport_iff corridor s n).2 le

theorem prefixSupport_subset_component
    (corridor : ColdCorridor.Corridor object windows component) (n : Nat) :
    corridor.prefixSupport n ⊆ component := by
  intro vertex mem
  obtain ⟨inner, _, rfl⟩ := (corridor.mem_prefixSupport n _).1 mem
  exact inner.2

theorem head_zero (corridor : ColdCorridor.Corridor object windows component) :
    corridor.head ⟨0, Nat.succ_pos _⟩ = corridor.entryStub.1 := by
  simp [ColdCorridor.Corridor.head, ColdCorridor.Corridor.entryStub,
    ColdCorridor.stubFoot]

theorem head_adj_succ (corridor : ColdCorridor.Corridor object windows component)
    (i : Nat) (hi : i < corridor.inside.1.length) :
    object.graph.Adj (corridor.head ⟨i, by omega⟩) (corridor.head ⟨i + 1, by omega⟩) :=
  SimpleGraph.induce_adj.mp (corridor.inside.1.adj_getVert_succ hi)

/-- The entry foot is on the cut boundary of every prefix: its window
neighbour lies outside the outside component. -/
theorem foot_mem_cutBoundary
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component) (n : Nat) :
    corridor.entryStub.1 ∈ SupportAtom.cutBoundary object (corridor.prefixSupport n) := by
  have stub := (ColdCorridor.mem_boundaryStubs_iff object windows component _).1
    (List.get_mem _ corridor.entry)
  rw [SupportAtom.mem_cutBoundary_iff]
  refine ⟨corridor.foot_mem_prefixSupport n, corridor.entryStub.2, stub.2.2, ?_⟩
  intro inside
  exact Finset.disjoint_left.mp outside.1
    (prefixSupport_subset_component corridor n inside) stub.2.1

/-- The head of an initial segment is on the cut boundary of its own prefix:
before the terminal segment its successor on the inside path is outside the
prefix; at the terminal segment it is the successor foot, whose window
endpoint is outside the component. -/
theorem head_mem_cutBoundary
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (right : corridor.Segment) :
    corridor.head right ∈
      SupportAtom.cutBoundary object (corridor.prefixSupport right.1) := by
  rw [SupportAtom.mem_cutBoundary_iff]
  refine ⟨(head_mem_prefixSupport_iff corridor right right.1).2 le_rfl, ?_⟩
  by_cases terminal : right.1 < corridor.inside.1.length
  · refine ⟨corridor.head ⟨right.1 + 1, by omega⟩, ?_, ?_⟩
    · exact head_adj_succ corridor right.1 terminal
    · rw [head_mem_prefixSupport_iff]; simp
  · have eq : right.1 = corridor.inside.1.length := by have := right.2; omega
    have stub := (ColdCorridor.mem_boundaryStubs_iff object windows component _).1
      (List.get_mem _ (ColdCorridor.successorIndex corridor.positive corridor.entry))
    have headEq : corridor.head right =
        ((ColdCorridor.boundaryStubs object windows component).get
          (ColdCorridor.successorIndex corridor.positive corridor.entry)).1 := by
      unfold ColdCorridor.Corridor.head
      rw [eq, SimpleGraph.Walk.getVert_length]
      rfl
    rw [headEq]
    refine ⟨_, stub.2.2, fun inside => ?_⟩
    exact Finset.disjoint_left.mp outside.1
      (prefixSupport_subset_component corridor right.1 inside) stub.2.1

/-- **Every equal-state pair is a boundary-degree separation of G's two
readings.**  For `left < right`,
`head right` is on the cut boundary of `J_right` and loses its corridor edge to
`head (right-1)` in the `J_left` reading. -/
theorem prefix_profile_ne
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (left right : corridor.Segment) (lt : left.1 < right.1) :
    (SupportAtom.retainedPiece object (corridor.prefixSupport right.1)
        (corridor.prefixSupport left.1)).boundaryDegreeProfile ≠
      (SupportAtom.retainedPiece object (corridor.prefixSupport right.1)
        (corridor.prefixSupport right.1)).boundaryDegreeProfile := by
  intro same
  let previous : corridor.Segment := ⟨right.1 - 1, by omega⟩
  have adj : object.graph.Adj (corridor.head right) (corridor.head previous) := by
    have := head_adj_succ corridor (right.1 - 1) (by have := right.2; omega)
    have e : (⟨right.1 - 1 + 1, by omega⟩ : corridor.Segment) = right :=
      Fin.ext (by simp; omega)
    rw [e] at this
    exact this.symm
  have prevIn : corridor.head previous ∈ corridor.prefixSupport right.1 :=
    (head_mem_prefixSupport_iff corridor previous right.1).2 (by simp [previous])
  have := retained_profile_eq_imp _ _ same (corridor.head right)
    (head_mem_cutBoundary outside corridor right) (corridor.head previous) prevIn adj
  have out := (head_mem_prefixSupport_iff corridor right left.1).1 this.1
  omega

end Corridor

/-- **Distinct states force a short first failure.**  If no two of the first
`first + 1` states agree, then `first < Q_cold`: they are distinct elements of
the `Q_cold`-element state type. -/
theorem first_lt_stateBound {object : FiniteObject.{v}}
    {windows component : Finset object.Vertex} {S : ColdCorridor.DeclaredSignature}
    (corridor : ColdCorridor.Corridor object windows component)
    (presentation : ColdCorridor.Presentation S object)
    (index : corridor.Segment → presentation.Segment)
    (first : corridor.Segment)
    (distinct : ∀ left right : corridor.Segment, left.1 < right.1 →
      right.1 ≤ first.1 →
        presentation.state (index left) ≠ presentation.state (index right)) :
    first.1 < ColdCorridor.stateBound S := by
  classical
  let f : Fin (first.1 + 1) → ColdCorridor.CutState S :=
    fun i => presentation.state (index ⟨i.1, by have := first.2; have := i.2; omega⟩)
  have inj : Function.Injective f := by
    intro i j e
    by_contra ne
    rcases Nat.lt_or_gt_of_ne (fun h => ne (Fin.ext h)) with h | h
    · exact distinct ⟨i.1, by have := first.2; have := i.2; omega⟩
        ⟨j.1, by have := first.2; have := j.2; omega⟩ h
        (by have := j.2; simp only; omega) e
    · exact distinct ⟨j.1, by have := first.2; have := j.2; omega⟩
        ⟨i.1, by have := first.2; have := i.2; omega⟩ h
        (by have := i.2; simp only; omega) e.symm
  have := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_fin] at this
  unfold ColdCorridor.stateBound
  omega


end Hypostructure.Graph.ColdEqualStates
