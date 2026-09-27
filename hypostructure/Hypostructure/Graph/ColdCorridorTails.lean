import Hypostructure.Graph.ColdGermFamily

/-!
# The two corridor segments at a vertex of a cold return corridor

`lem:absorbed-germ-fan-data` (ii) (tex 7926-7952): when the first-failure
support of a selected half-edge `ε` contains a vertex `z` of degree at least
`4`, "the corridor enters `z` through one of its incidences and leaves through
another", and "the segments of the corridor on either side of `z` are two
connector tails separated at `z`".

The cold return corridor of `ε` is the entry stub `hᵢ`, the inside path from its
outside foot to the successor foot, and the successor stub `hᵢ₊₁`.  At the
vertex `z` reached at index `i` of the inside path this module names

* the **entry-side incidence** of `z` (`entryNeighbour`): the previous inside
  vertex, or the entry stub's window endpoint when `z` is the entry foot;
* the **exit-side incidence** (`exitNeighbour`): the next inside vertex, or the
  successor stub's window endpoint when `z` is the successor foot;
* the two **corridor segments** at `z`, read away from `z`: `entryTail`
  (back to the foot, then across `ε` into its window) and `exitTail` (on to the
  successor foot, then across `hᵢ₊₁` into its window).

Both are simple walks of the object that avoid `z`, begin at the corresponding
incidence, and the two incidences are distinct.  Everything is read off the
corridor itself; this module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.ColdCorridor

universe u

variable {object : FiniteObject.{u}} {windows component : Finset object.Vertex}

namespace Corridor

variable (corridor : Corridor object windows component)

/-- The vertex of the object at index `j` of the inside path. -/
noncomputable def vertexAt (j : Nat) : object.Vertex :=
  (corridor.inside.1.getVert j).1

theorem vertexAt_mem (j : Nat) : corridor.vertexAt j ∈ component :=
  (corridor.inside.1.getVert j).2

theorem vertexAt_adj {j : Nat} (bound : j < corridor.inside.1.length) :
    object.graph.Adj (corridor.vertexAt j) (corridor.vertexAt (j + 1)) :=
  corridor.inside.1.adj_getVert_succ bound

theorem vertexAt_inj {i j : Nat} (iLe : i ≤ corridor.inside.1.length)
    (jLe : j ≤ corridor.inside.1.length)
    (same : corridor.vertexAt i = corridor.vertexAt j) : i = j :=
  corridor.inside.2.getVert_injOn iLe jLe (Subtype.ext same)

theorem vertexAt_eq_head (segment : corridor.Segment) :
    corridor.vertexAt segment.1 = corridor.head segment := rfl

theorem vertexAt_zero : corridor.vertexAt 0 = corridor.entryStub.1 := by
  simp [vertexAt, stubFoot, Corridor.entryStub]

theorem vertexAt_length :
    corridor.vertexAt corridor.inside.1.length = corridor.successorStub.1 := by
  simp [vertexAt, stubFoot, Corridor.successorStub]

theorem entryStub_isStub :
    IsBoundaryStub object windows component corridor.entryStub :=
  (mem_boundaryStubs_iff object windows component _).1 (List.get_mem _ _)

theorem successorStub_isStub :
    IsBoundaryStub object windows component corridor.successorStub :=
  (mem_boundaryStubs_iff object windows component _).1 (List.get_mem _ _)

theorem entryStub_window_not_mem (outside : IsOutsideComponent object windows component) :
    corridor.entryStub.2 ∉ component := fun member =>
  Finset.disjoint_left.mp outside.1 member corridor.entryStub_isStub.2.1

theorem successorStub_window_not_mem
    (outside : IsOutsideComponent object windows component) :
    corridor.successorStub.2 ∉ component := fun member =>
  Finset.disjoint_left.mp outside.1 member corridor.successorStub_isStub.2.1

/-- The two stubs of a corridor are distinct. -/
theorem entryStub_ne_successorStub :
    corridor.entryStub ≠ corridor.successorStub := by
  intro same
  have indices := (List.Nodup.get_inj_iff
    (boundaryStubs_nodup object windows component)).1
    (show (boundaryStubs object windows component).get corridor.entry =
      (boundaryStubs object windows component).get
        (successorIndex corridor.positive corridor.entry) from same)
  have values := congrArg Fin.val indices
  have two := corridor.twoStubs
  have entryLt := corridor.entry.2
  simp only [successorIndex] at values
  rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt entryLt) with last | small
  · rw [show corridor.entry.1 + 1 = (boundaryStubs object windows component).length
      from last, Nat.mod_self] at values
    omega
  · rw [Nat.mod_eq_of_lt small] at values
    omega

/-! ### The corridor segments -/

/-- `ent i`: the inside vertices `i−1, …, 0` followed by the entry stub's
window endpoint. -/
noncomputable def entryTail : Nat → List object.Vertex
  | 0 => [corridor.entryStub.2]
  | i + 1 => corridor.vertexAt i :: entryTail i

/-- `seg k n`: the `n` inside vertices `k, …, k+n−1` followed by the successor
stub's window endpoint. -/
noncomputable def forwardSegment : Nat → Nat → List object.Vertex
  | _, 0 => [corridor.successorStub.2]
  | k, n + 1 => corridor.vertexAt k :: forwardSegment (k + 1) n

/-- The exit-side segment at index `i`: the inside vertices `i+1, …, length`
followed by the successor stub's window endpoint. -/
noncomputable def exitTail (i : Nat) : List object.Vertex :=
  corridor.forwardSegment (i + 1) (corridor.inside.1.length - i)

/-- The entry-side incidence of the vertex at index `i`. -/
noncomputable def entryNeighbour (i : Nat) : object.Vertex :=
  match i with
  | 0 => corridor.entryStub.2
  | i + 1 => corridor.vertexAt i

/-- The exit-side incidence of the vertex at index `i`. -/
noncomputable def exitNeighbour (i : Nat) : object.Vertex :=
  if i < corridor.inside.1.length then corridor.vertexAt (i + 1)
  else corridor.successorStub.2

theorem mem_entryTail {i : Nat} {vertex : object.Vertex} :
    vertex ∈ corridor.entryTail i ↔
      (∃ j < i, vertex = corridor.vertexAt j) ∨ vertex = corridor.entryStub.2 := by
  induction i with
  | zero => simp [entryTail]
  | succ i ih =>
      simp only [entryTail, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨j, lt, rfl⟩ | rfl)
        · exact Or.inl ⟨i, Nat.lt_succ_self _, rfl⟩
        · exact Or.inl ⟨j, Nat.lt_succ_of_lt lt, rfl⟩
        · exact Or.inr rfl
      · rintro (⟨j, lt, rfl⟩ | rfl)
        · rcases Nat.lt_succ_iff_lt_or_eq.mp lt with lt | rfl
          · exact Or.inr (Or.inl ⟨j, lt, rfl⟩)
          · exact Or.inl rfl
        · exact Or.inr (Or.inr rfl)

theorem mem_forwardSegment {k n : Nat} {vertex : object.Vertex} :
    vertex ∈ corridor.forwardSegment k n ↔
      (∃ j, k ≤ j ∧ j < k + n ∧ vertex = corridor.vertexAt j) ∨
        vertex = corridor.successorStub.2 := by
  induction n generalizing k with
  | zero =>
      simp only [forwardSegment, List.mem_singleton]
      constructor
      · exact Or.inr
      · rintro (⟨j, le, lt, _⟩ | rfl)
        · omega
        · rfl
  | succ n ih =>
      simp only [forwardSegment, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨j, le, lt, rfl⟩ | rfl)
        · exact Or.inl ⟨k, le_refl _, by omega, rfl⟩
        · exact Or.inl ⟨j, by omega, by omega, rfl⟩
        · exact Or.inr rfl
      · rintro (⟨j, le, lt, rfl⟩ | rfl)
        · rcases Nat.eq_or_lt_of_le le with rfl | lt'
          · exact Or.inl rfl
          · exact Or.inr (Or.inl ⟨j, by omega, by omega, rfl⟩)
        · exact Or.inr (Or.inr rfl)

theorem mem_exitTail {i : Nat} (iLe : i ≤ corridor.inside.1.length)
    {vertex : object.Vertex} :
    vertex ∈ corridor.exitTail i ↔
      (∃ j, i < j ∧ j ≤ corridor.inside.1.length ∧ vertex = corridor.vertexAt j) ∨
        vertex = corridor.successorStub.2 := by
  rw [exitTail, mem_forwardSegment]
  constructor
  · rintro (⟨j, le, lt, rfl⟩ | rfl)
    · exact Or.inl ⟨j, by omega, by omega, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨j, lt, le, rfl⟩ | rfl)
    · exact Or.inl ⟨j, by omega, by omega, rfl⟩
    · exact Or.inr rfl

theorem entryTail_head? (i : Nat) :
    (corridor.entryTail i).head? = some (corridor.entryNeighbour i) := by
  cases i <;> rfl

theorem exitTail_head? (i : Nat) :
    (corridor.exitTail i).head? = some (corridor.exitNeighbour i) := by
  unfold exitTail exitNeighbour
  split
  · next lt =>
      obtain ⟨n, hn⟩ : ∃ n, corridor.inside.1.length - i = n + 1 :=
        ⟨corridor.inside.1.length - i - 1, by omega⟩
      rw [hn]
      rfl
  · next notLt =>
      rw [show corridor.inside.1.length - i = 0 by omega]
      rfl

theorem entryTail_isChain (i : Nat) (iLe : i ≤ corridor.inside.1.length) :
    (corridor.entryTail i).IsChain object.graph.Adj := by
  induction i with
  | zero => simp [entryTail]
  | succ i ih =>
      have rest := ih (by omega)
      simp only [entryTail]
      refine List.IsChain.cons rest (fun next member => ?_)
      rw [entryTail_head?, Option.mem_some_iff] at member
      subst member
      cases i with
      | zero =>
          simpa [entryNeighbour, vertexAt_zero] using corridor.entryStub_isStub.2.2
      | succ i =>
          exact (corridor.vertexAt_adj (by omega)).symm

theorem forwardSegment_isChain :
    ∀ (n k : Nat), k + n = corridor.inside.1.length + 1 →
      (corridor.forwardSegment k n).IsChain object.graph.Adj
  | 0, _, _ => by simp [forwardSegment]
  | n + 1, k, sum => by
      have rest := forwardSegment_isChain n (k + 1) (by omega)
      simp only [forwardSegment]
      refine List.IsChain.cons rest (fun next member => ?_)
      cases n with
      | zero =>
          simp only [forwardSegment, List.head?_cons, Option.mem_some_iff] at member
          subst member
          have kEq : k = corridor.inside.1.length := by omega
          rw [kEq, vertexAt_length]
          exact corridor.successorStub_isStub.2.2
      | succ n =>
          simp only [forwardSegment, List.head?_cons, Option.mem_some_iff] at member
          subst member
          exact corridor.vertexAt_adj (by omega)

theorem exitTail_isChain (i : Nat) (iLe : i ≤ corridor.inside.1.length) :
    (corridor.exitTail i).IsChain object.graph.Adj :=
  corridor.forwardSegment_isChain _ _ (by omega)

theorem entryTail_nodup (outside : IsOutsideComponent object windows component)
    (i : Nat) (iLe : i ≤ corridor.inside.1.length) :
    (corridor.entryTail i).Nodup := by
  induction i with
  | zero => simp [entryTail]
  | succ i ih =>
      simp only [entryTail]
      refine List.nodup_cons.mpr ⟨?_, ih (by omega)⟩
      intro member
      rcases (corridor.mem_entryTail).1 member with ⟨j, lt, same⟩ | same
      · have := corridor.vertexAt_inj (by omega) (by omega) same
        omega
      · exact corridor.entryStub_window_not_mem outside
          (same ▸ corridor.vertexAt_mem i)

theorem exitTail_nodup (outside : IsOutsideComponent object windows component)
    (i : Nat) (iLe : i ≤ corridor.inside.1.length) :
    (corridor.exitTail i).Nodup := by
  have general : ∀ (n k : Nat), k + n = corridor.inside.1.length + 1 →
      (corridor.forwardSegment k n).Nodup := by
    intro n
    induction n with
    | zero => intro k _; simp [forwardSegment]
    | succ n ih =>
        intro k sum
        simp only [forwardSegment]
        refine List.nodup_cons.mpr ⟨?_, ih (k + 1) (by omega)⟩
        intro member
        rcases (corridor.mem_forwardSegment).1 member with ⟨j, le, lt, same⟩ | same
        · have := corridor.vertexAt_inj (by omega) (by omega) same
          omega
        · exact corridor.successorStub_window_not_mem outside
            (same ▸ corridor.vertexAt_mem k)
  exact general _ _ (by omega)

/-- The vertex at index `i` is on neither of its two segments. -/
theorem vertexAt_not_mem_entryTail
    (outside : IsOutsideComponent object windows component)
    {i : Nat} (iLe : i ≤ corridor.inside.1.length) :
    corridor.vertexAt i ∉ corridor.entryTail i := by
  intro member
  rcases (corridor.mem_entryTail).1 member with ⟨j, lt, same⟩ | same
  · have := corridor.vertexAt_inj iLe (by omega) same
    omega
  · exact corridor.entryStub_window_not_mem outside (same ▸ corridor.vertexAt_mem i)

theorem vertexAt_not_mem_exitTail
    (outside : IsOutsideComponent object windows component)
    {i : Nat} (iLe : i ≤ corridor.inside.1.length) :
    corridor.vertexAt i ∉ corridor.exitTail i := by
  intro member
  rcases (corridor.mem_exitTail iLe).1 member with ⟨j, lt, le, same⟩ | same
  · have := corridor.vertexAt_inj iLe le same
    omega
  · exact corridor.successorStub_window_not_mem outside
      (same ▸ corridor.vertexAt_mem i)

/-- The two incidences are neighbours of the vertex. -/
theorem adj_entryNeighbour {i : Nat} (iLe : i ≤ corridor.inside.1.length) :
    object.graph.Adj (corridor.vertexAt i) (corridor.entryNeighbour i) := by
  cases i with
  | zero => simpa [entryNeighbour, vertexAt_zero] using corridor.entryStub_isStub.2.2
  | succ i => exact (corridor.vertexAt_adj (by omega)).symm

theorem adj_exitNeighbour {i : Nat} (iLe : i ≤ corridor.inside.1.length) :
    object.graph.Adj (corridor.vertexAt i) (corridor.exitNeighbour i) := by
  unfold exitNeighbour
  split
  · next lt => exact corridor.vertexAt_adj lt
  · next notLt =>
      have iEq : i = corridor.inside.1.length := by omega
      rw [iEq, vertexAt_length]
      exact corridor.successorStub_isStub.2.2

/-- **"The two corridor incidences at `z` are distinct."** -/
theorem entryNeighbour_ne_exitNeighbour
    (outside : IsOutsideComponent object windows component)
    {i : Nat} (iLe : i ≤ corridor.inside.1.length) :
    corridor.entryNeighbour i ≠ corridor.exitNeighbour i := by
  intro same
  unfold exitNeighbour at same
  cases i with
  | zero =>
      simp only [entryNeighbour] at same
      split at same
      · exact corridor.entryStub_window_not_mem outside
          (same ▸ corridor.vertexAt_mem 1)
      · next notLt =>
          have zero : corridor.inside.1.length = 0 := by omega
          apply corridor.entryStub_ne_successorStub
          refine Prod.ext ?_ same
          rw [← vertexAt_zero, ← vertexAt_length, zero]
  | succ i =>
      simp only [entryNeighbour] at same
      split at same
      · have := corridor.vertexAt_inj (by omega) (by omega) same
        omega
      · exact corridor.successorStub_window_not_mem outside
          (same ▸ corridor.vertexAt_mem i)

/-! ### The entry foot

When the vertex is the entry foot (index `0`), the entry-side segment is the
entry stub's window endpoint alone: "the corridor enters `z` through" `ε`
itself.  That segment lies in the deleted windows, so it meets no set disjoint
from them. -/

theorem entryTail_zero : corridor.entryTail 0 = [corridor.entryStub.2] := rfl

/-- At the entry foot, the entry-side segment meets no vertex outside the
deleted windows. -/
theorem entryTail_zero_not_meets {core : Finset object.Vertex}
    (away : Disjoint core windows) :
    ¬ ∃ vertex ∈ corridor.entryTail 0, vertex ∈ core := by
  rintro ⟨vertex, member, inCore⟩
  rw [entryTail_zero, List.mem_singleton] at member
  subst member
  exact Finset.disjoint_left.mp away inCore corridor.entryStub_isStub.2.1

end Corridor

end Hypostructure.Graph.ColdCorridor
