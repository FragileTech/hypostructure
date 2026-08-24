import Hypostructure.Graph.Gluing
import Hypostructure.Graph.RootedReturn
import Hypostructure.Graph.Response

/-!
# Crossing cycles of a boundaried gluing

The semantic step of `lem:typeA-visible-entry` evaluates the cycle target on a
glued reading: a context-side path and a piece-side path between the same two
boundary labels close a cycle of the gluing whose length is the sum of the two
path lengths.  The piece and context interiors are disjoint by construction of
the glued carrier, so the only sharing to control is at boundary labels, and a
context path whose interior avoids the boundary shares exactly the two
endpoints.  Nothing here mentions a support, a target algebra, or a paper
constant: the target predicate is a parameter.
-/

namespace Hypostructure.Graph

universe u

variable {boundary : Boundary.{u}}

/-- The atom side maps into the gluing. -/
def pieceHom (piece : BoundaryPiece boundary)
    (outside : OutsideContext boundary) :
    piece.graph →g (glue piece outside).graph where
  toFun := pieceEmbedding piece outside
  map_rel' := by
    intro left right adjacent
    exact (glueGraph_adj_iff piece outside _ _).mpr
      (Or.inl ⟨left, right, adjacent, rfl, rfl⟩)

/-- The context side maps into the gluing. -/
def contextHom (piece : BoundaryPiece boundary)
    (outside : OutsideContext boundary) :
    outside.graph →g (glue piece outside).graph where
  toFun := contextEmbedding piece outside
  map_rel' := by
    intro left right adjacent
    exact (glueGraph_adj_iff piece outside _ _).mpr
      (Or.inr ⟨left, right, adjacent, rfl, rfl⟩)

@[simp] theorem pieceHom_boundary (piece : BoundaryPiece boundary)
    (outside : OutsideContext boundary) (label : boundary.Vertex) :
    pieceHom piece outside (.inl label) = .inl label := rfl

@[simp] theorem contextHom_boundary (piece : BoundaryPiece boundary)
    (outside : OutsideContext boundary) (label : boundary.Vertex) :
    contextHom piece outside (.inl label) = .inl label := rfl

/-- **A piece path and a context path between the same two boundary labels
close a crossing cycle of the gluing**, provided the context path's interior
avoids the boundary.  Its length is the sum of the two path lengths. -/
theorem hasCycleWithLength_glue_of_crossing
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    {left right : boundary.Vertex}
    (pieceWalk : piece.graph.Walk (.inl left) (.inl right))
    (contextWalk : outside.graph.Walk (.inl left) (.inl right))
    (piecePath : pieceWalk.IsPath) (contextPath : contextWalk.IsPath)
    (contextInterior : ∀ label : boundary.Vertex,
      (Sum.inl label : boundary.Vertex ⊕ outside.Internal) ∈
        contextWalk.support → label = left ∨ label = right)
    (nondegenerate : 1 < pieceWalk.length ∨ 1 < contextWalk.length)
    {LengthOK : Nat → Prop}
    (accepted : LengthOK (pieceWalk.length + contextWalk.length)) :
    HasCycleWithLength LengthOK (glue piece outside) := by
  classical
  let forward : (glue piece outside).graph.Walk (.inl left) (.inl right) :=
    pieceWalk.map (pieceHom piece outside)
  let backward : (glue piece outside).graph.Walk (.inl left) (.inl right) :=
    contextWalk.map (contextHom piece outside)
  have forwardPath : forward.IsPath :=
    SimpleGraph.Walk.map_isPath_of_injective
      (pieceEmbedding piece outside).injective piecePath
  have backwardPath : backward.IsPath :=
    SimpleGraph.Walk.map_isPath_of_injective
      (contextEmbedding piece outside).injective contextPath
  have disjointTails :
      forward.support.tail.Disjoint backward.reverse.support.tail := by
    intro vertex forwardMember backwardMember
    have forwardSupport : vertex ∈ forward.support :=
      List.mem_of_mem_tail forwardMember
    have backwardSupport : vertex ∈ backward.support := by
      have := List.mem_of_mem_tail backwardMember
      simpa [SimpleGraph.Walk.support_reverse] using this
    -- the vertex lies on both mapped walks, so it is a boundary label
    have forwardList : vertex ∈
        pieceWalk.support.map (pieceHom piece outside) := by
      rw [← SimpleGraph.Walk.support_map]
      exact forwardSupport
    have backwardList : vertex ∈
        contextWalk.support.map (contextHom piece outside) := by
      rw [← SimpleGraph.Walk.support_map]
      exact backwardSupport
    obtain ⟨pieceVertex, _pieceMember, pieceEq⟩ := List.mem_map.mp forwardList
    obtain ⟨contextVertex, contextMember, contextEq⟩ :=
      List.mem_map.mp backwardList
    have boundaryLabel : ∃ label : boundary.Vertex, vertex = .inl label := by
      rcases pieceVertex with pieceLabel | pieceInside
      · exact ⟨pieceLabel, pieceEq.symm⟩
      · rcases contextVertex with contextLabel | contextInside
        · exact ⟨contextLabel, contextEq.symm⟩
        · rw [← pieceEq] at contextEq
          have impossible : (Sum.inr (Sum.inr contextInside) :
              GluedVertex piece outside) = Sum.inr (Sum.inl pieceInside) :=
            contextEq
          simp at impossible
    obtain ⟨label, rfl⟩ := boundaryLabel
    have contextLabelMember :
        (Sum.inl label : boundary.Vertex ⊕ outside.Internal) ∈
          contextWalk.support := by
      rcases contextVertex with contextLabel | contextInside
      · have inlEq : (Sum.inl contextLabel : GluedVertex piece outside) =
            Sum.inl label := contextEq
        have labelEq : contextLabel = label := by simpa using inlEq
        subst labelEq
        exact contextMember
      · have impossible : (Sum.inr (Sum.inr contextInside) :
            GluedVertex piece outside) = Sum.inl label := contextEq
        simp at impossible
    rcases contextInterior label contextLabelMember with eqLeft | eqRight
    · -- `left` heads the forward path, so it is not on the forward tail
      have nodup : ((Sum.inl left : (glue piece outside).Vertex) ::
          forward.support.tail).Nodup := by
        have := forwardPath.support_nodup
        rwa [← SimpleGraph.Walk.cons_tail_support forward] at this
      rw [eqLeft] at forwardMember
      exact absurd forwardMember (List.nodup_cons.mp nodup).1
    · -- `right` heads the reversed backward path
      have nodup : ((Sum.inl right : (glue piece outside).Vertex) ::
          backward.reverse.support.tail).Nodup := by
        have := backwardPath.reverse.support_nodup
        rwa [← SimpleGraph.Walk.cons_tail_support backward.reverse] at this
      rw [eqRight] at backwardMember
      exact absurd backwardMember (List.nodup_cons.mp nodup).1
  let pair : CommonEndpointsCycle (glue piece outside) :=
    { ends := (.inl left, .inl right)
      forward := forward
      backward := backward
      forward_isPath := forwardPath
      backward_isPath := backwardPath
      internallyDisjoint := disjointTails
      nondegenerate := by
        rcases nondegenerate with pieceLong | contextLong
        · left
          show 1 < (pieceWalk.map (pieceHom piece outside)).length
          rw [SimpleGraph.Walk.length_map]
          exact pieceLong
        · right
          show 1 < (contextWalk.map (contextHom piece outside)).length
          rw [SimpleGraph.Walk.length_map]
          exact contextLong }
  refine ⟨pair.target LengthOK ?_⟩
  show LengthOK ((pieceWalk.map (pieceHom piece outside)).length +
    (contextWalk.map (contextHom piece outside)).length)
  rw [SimpleGraph.Walk.length_map, SimpleGraph.Walk.length_map]
  exact accepted


/-! ## The synthetic path context

`Response.TargetDefect` quantifies over every outside context of the labelled
interface.  The distinguishing context the manuscript's spectral arguments
construct is the simplest one: a bare path of a chosen length between two
selected boundary labels, with every other label isolated.  Its cycles through
the gluing are exactly the piece paths between the two labels, shifted by the
chosen length. -/

/-- The support list of the synthetic path: the first label, the chain of
`k` fresh internal vertices, the second label. -/
def pathContextList (boundary : Boundary.{u}) (first second : boundary.Vertex)
    (k : Nat) : List (boundary.Vertex ⊕ ULift.{u} (Fin k)) :=
  .inl first ::
    (List.ofFn (fun index : Fin k => Sum.inr (ULift.up index))) ++
      [.inl second]

/-- The chain relation of the synthetic path. -/
def PathContextRel (boundary : Boundary.{u}) (first second : boundary.Vertex)
    (k : Nat) :
    (boundary.Vertex ⊕ ULift.{u} (Fin k)) →
      (boundary.Vertex ⊕ ULift.{u} (Fin k)) → Prop :=
  fun left right =>
    ∃ position : Nat,
      (pathContextList boundary first second k)[position]? = some left ∧
        (pathContextList boundary first second k)[position + 1]? = some right

/-- **The synthetic path context**: a single path of length `k + 1` from
`first` to `second` through `k` fresh internal vertices; every other boundary
label is isolated. -/
@[reducible] noncomputable def pathContext (boundary : Boundary.{u})
    (first second : boundary.Vertex) (k : Nat) :
    OutsideContext boundary where
  Internal := ULift.{u} (Fin k)
  internalVertices := by
    exact FinEnum.ofEquiv (Fin k) Equiv.ulift
  graph := SimpleGraph.fromRel (PathContextRel boundary first second k)
  decideAdj := Classical.decRel _


namespace PathContext

variable {boundary : Boundary.{u}} {first second : boundary.Vertex} {k : Nat}

theorem pathContextList_ne_nil :
    pathContextList boundary first second k ≠ [] := by
  simp [pathContextList]

theorem pathContextList_length :
    (pathContextList boundary first second k).length = k + 2 := by
  simp [pathContextList]

theorem pathContextList_nodup (firstNe : first ≠ second) :
    (pathContextList boundary first second k).Nodup := by
  refine List.nodup_cons.mpr ⟨?_, ?_⟩
  · simp [List.mem_ofFn, firstNe]
  · refine List.Nodup.append ?_ (List.nodup_singleton _) ?_
    · exact List.nodup_ofFn.mpr fun leftIndex rightIndex equal => by
        simpa using equal
    · intro vertex vertexMember singletonMember
      rw [List.mem_singleton] at singletonMember
      subst singletonMember
      simp [List.mem_ofFn] at vertexMember

/-- The synthetic path's list is a chain of its own graph. -/
theorem pathContextList_isChain (firstNe : first ≠ second) :
    (pathContextList boundary first second k).IsChain
      (pathContext boundary first second k).graph.Adj := by
  rw [List.isChain_iff_getElem]
  intro index bound
  have distinct :
      (pathContextList boundary first second k)[index]'
          (Nat.lt_of_succ_lt bound) ≠
        (pathContextList boundary first second k)[index + 1]'bound := by
    intro equal
    have := (List.Nodup.getElem_inj_iff
      (pathContextList_nodup (k := k) firstNe)).mp equal
    omega
  refine (SimpleGraph.fromRel_adj _ _ _).mpr ⟨distinct, Or.inl ?_⟩
  refine ⟨index, ?_, ?_⟩
  · exact List.getElem?_eq_getElem (Nat.lt_of_succ_lt bound)
  · exact List.getElem?_eq_getElem bound

theorem pathContextList_getLast :
    (pathContextList boundary first second k).getLast
      pathContextList_ne_nil = Sum.inl second := by
  have lastEq :
      (pathContextList boundary first second k).getLast? =
        some (Sum.inl second) := by
    show ((Sum.inl first ::
        List.ofFn (fun index : Fin k => Sum.inr (ULift.up index))) ++
          [Sum.inl second]).getLast? = some (Sum.inl second)
    rw [List.getLast?_append_of_ne_nil _ (by simp)]
    rfl
  have lastSome := List.getLast?_eq_some_getLast
    (l := pathContextList boundary first second k) pathContextList_ne_nil
  rw [lastSome] at lastEq
  exact Option.some_inj.mp lastEq

/-- The canonical walk of the synthetic path context. -/
noncomputable def walk (firstNe : first ≠ second) :
    (pathContext boundary first second k).graph.Walk
      (.inl first) (.inl second) :=
  (SimpleGraph.Walk.ofSupport
    (pathContextList boundary first second k)
    pathContextList_ne_nil (pathContextList_isChain firstNe)).copy rfl
    pathContextList_getLast

@[simp] theorem walk_support (firstNe : first ≠ second) :
    (walk (k := k) firstNe).support = pathContextList boundary first second k := by
  unfold walk
  simp only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_ofSupport]

@[simp] theorem walk_length (firstNe : first ≠ second) :
    (walk (k := k) firstNe).length = k + 1 := by
  unfold walk
  simp only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_ofSupport,
    pathContextList_length]
  omega

theorem walk_isPath (firstNe : first ≠ second) :
    (walk (k := k) firstNe).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, walk_support]
  exact pathContextList_nodup firstNe

/-- The synthetic path meets the boundary only at its two endpoints. -/
theorem walk_boundary (firstNe : first ≠ second)
    (label : boundary.Vertex)
    (member : (Sum.inl label :
        boundary.Vertex ⊕ (pathContext boundary first second k).Internal) ∈
      (walk (k := k) firstNe).support) :
    label = first ∨ label = second := by
  rw [walk_support] at member
  have member' : (Sum.inl label : boundary.Vertex ⊕ ULift.{u} (Fin k)) ∈
      Sum.inl first ::
        (List.ofFn (fun index : Fin k => Sum.inr (ULift.up index)) ++
          [Sum.inl second]) := member
  rcases List.eq_or_mem_of_mem_cons member' with headEq | tailMember
  · exact Or.inl (by simpa using headEq)
  · rcases List.mem_append.mp tailMember with ofFnMember | lastMember
    · obtain ⟨index, indexEq⟩ := List.mem_ofFn.mp ofFnMember
      simp at indexEq
    · rw [List.mem_singleton] at lastMember
      exact Or.inr (by simpa using lastMember)

/-- **The positive direction of the synthetic-context evaluation**: a piece
path between the two selected labels closes an accepted crossing cycle with
the synthetic path, so the glued reading realizes the target. -/
theorem hasCycleWithLength_glue_pathContext
    {piece : BoundaryPiece boundary} (firstNe : first ≠ second)
    (kPos : 1 ≤ k)
    (pieceWalk : piece.graph.Walk (.inl first) (.inl second))
    (piecePath : pieceWalk.IsPath)
    {LengthOK : Nat → Prop}
    (accepted : LengthOK (pieceWalk.length + (k + 1))) :
    HasCycleWithLength LengthOK
      (glue piece (pathContext boundary first second k)) := by
  refine hasCycleWithLength_glue_of_crossing piece
    (pathContext boundary first second k) pieceWalk (walk firstNe) piecePath
    (walk_isPath firstNe) ?_ ?_ ?_
  · intro label member
    exact walk_boundary firstNe label member
  · right
    rw [walk_length]
    omega
  · rw [walk_length]
    exact accepted

/-! ### The chain's exact index layout -/

theorem pathContextList_getElem_zero :
    (pathContextList boundary first second k)[0]'(by
      rw [pathContextList_length]; omega) = Sum.inl first := rfl

theorem pathContextList_getElem_succ {j : Nat} (bound : j < k) :
    (pathContextList boundary first second k)[j + 1]'(by
      rw [pathContextList_length]; omega) =
        Sum.inr (ULift.up ⟨j, bound⟩) := by
  show ((List.ofFn (fun index : Fin k => Sum.inr (ULift.up index))) ++
      [Sum.inl second])[j]'(by simp; omega) = _
  rw [List.getElem_append_left (by simpa using bound)]
  simp

theorem pathContextList_getElem_last :
    (pathContextList boundary first second k)[k + 1]'(by
      rw [pathContextList_length]; omega) = Sum.inl second := by
  show ((List.ofFn (fun index : Fin k => Sum.inr (ULift.up index))) ++
      [Sum.inl second])[k]'(by simp) = _
  rw [List.getElem_append_right (by simp)]
  simp

/-- A value determines its position on the (nodup) chain list. -/
theorem pathContextList_position_unique (firstNe : first ≠ second)
    {position : Nat} {value : boundary.Vertex ⊕ ULift.{u} (Fin k)}
    (found : (pathContextList boundary first second k)[position]? = some value)
    {other : Nat}
    (foundOther :
      (pathContextList boundary first second k)[other]? = some value) :
    position = other := by
  obtain ⟨positionLt, positionEq⟩ := List.getElem?_eq_some_iff.mp found
  obtain ⟨otherLt, otherEq⟩ := List.getElem?_eq_some_iff.mp foundOther
  exact (List.Nodup.getElem_inj_iff
    (pathContextList_nodup (k := k) firstNe)).mp
    (positionEq.trans otherEq.symm)

/-- **The chain relation at an internal chain vertex is exactly its
predecessor/successor pair.** -/
theorem pathContextRel_chain_iff (firstNe : first ≠ second)
    {j : Nat} (bound : j < k)
    (other : boundary.Vertex ⊕ ULift.{u} (Fin k)) :
    (PathContextRel boundary first second k
        (Sum.inr (ULift.up ⟨j, bound⟩)) other ∨
      PathContextRel boundary first second k other
        (Sum.inr (ULift.up ⟨j, bound⟩))) ↔
      other = (pathContextList boundary first second k)[j]'(by
          rw [pathContextList_length]; omega) ∨
        other = (pathContextList boundary first second k)[j + 2]'(by
          rw [pathContextList_length]; omega) := by
  have selfAt : (pathContextList boundary first second k)[j + 1]? =
      some (Sum.inr (ULift.up ⟨j, bound⟩)) := by
    rw [List.getElem?_eq_getElem (by rw [pathContextList_length]; omega)]
    exact congrArg some (pathContextList_getElem_succ bound)
  constructor
  · rintro (⟨position, atPosition, atNext⟩ | ⟨position, atPosition, atNext⟩)
    · -- the vertex sits at `position`, so `position = j + 1`
      have positionEq : position = j + 1 :=
        pathContextList_position_unique firstNe atPosition selfAt
      subst positionEq
      obtain ⟨_, nextEq⟩ := List.getElem?_eq_some_iff.mp atNext
      exact Or.inr nextEq.symm
    · have positionEq : position + 1 = j + 1 :=
        pathContextList_position_unique firstNe atNext selfAt
      have positionEq' : position = j := by omega
      subst positionEq'
      obtain ⟨_, atEq⟩ := List.getElem?_eq_some_iff.mp atPosition
      exact Or.inl atEq.symm
  · rintro (rfl | rfl)
    · refine Or.inr ⟨j, ?_, ?_⟩
      · exact List.getElem?_eq_getElem _
      · exact selfAt
    · refine Or.inl ⟨j + 1, selfAt, ?_⟩
      exact List.getElem?_eq_getElem _

/-- **The gluing's neighbourhood at a chain vertex is exactly the chain's
predecessor/successor pair.**  The atom side never reaches a context-internal
vertex, and the synthetic relation is the chain. -/
theorem glue_adj_chain {piece : BoundaryPiece boundary}
    (firstNe : first ≠ second) {j : Nat} (bound : j < k)
    (other : GluedVertex piece (pathContext boundary first second k)) :
    (glue piece (pathContext boundary first second k)).graph.Adj
        (contextEmbedding piece (pathContext boundary first second k)
          (Sum.inr (ULift.up ⟨j, bound⟩))) other ↔
      (other = contextEmbedding piece (pathContext boundary first second k)
          ((pathContextList boundary first second k)[j]'(by
            rw [pathContextList_length]; omega)) ∨
        other = contextEmbedding piece (pathContext boundary first second k)
          ((pathContextList boundary first second k)[j + 2]'(by
            rw [pathContextList_length]; omega))) := by
  constructor
  · intro adjacent
    rcases (glueGraph_adj_iff piece
        (pathContext boundary first second k) _ _).mp adjacent with
      ⟨pieceLeft, _pieceRight, _adj, leftEq, _rightEq⟩ |
      ⟨contextLeft, contextRight, adj, leftEq, rightEq⟩
    · -- the atom side cannot own a context-internal endpoint
      exfalso
      rcases pieceLeft with label | inside
      · exact absurd leftEq (by simp [pieceEmbedding, contextEmbedding])
      · exact absurd leftEq (by simp [pieceEmbedding, contextEmbedding])
    · have contextLeftEq : contextLeft =
          Sum.inr (ULift.up ⟨j, bound⟩) := by
        rcases contextLeft with label | inside
        · exact absurd leftEq (by simp [contextEmbedding])
        · have : (Sum.inr inside :
              boundary.Vertex ⊕ ULift.{u} (Fin k)) =
                Sum.inr (ULift.up ⟨j, bound⟩) := by
            have inrEq : (Sum.inr (Sum.inr inside) :
                GluedVertex piece (pathContext boundary first second k)) =
                  Sum.inr (Sum.inr (ULift.up ⟨j, bound⟩)) := leftEq
            simpa using inrEq
          exact this
      subst contextLeftEq
      have related := (SimpleGraph.fromRel_adj _ _ _).mp adj
      rcases (pathContextRel_chain_iff firstNe bound contextRight).mp
          related.2 with atPred | atSucc
      · exact Or.inl (by rw [← rightEq, atPred])
      · exact Or.inr (by rw [← rightEq, atSucc])
  · intro branch
    have selfSucc :
        (pathContextList boundary first second k)[j + 1]'(by
          rw [pathContextList_length]; omega) =
          Sum.inr (ULift.up ⟨j, bound⟩) :=
      pathContextList_getElem_succ bound
    have neighbourNe : ∀ (position : Nat)
        (positionLt : position < (pathContextList boundary first second
          k).length), position ≠ j + 1 →
        (pathContextList boundary first second k)[position] ≠
          Sum.inr (ULift.up ⟨j, bound⟩) := by
      intro position positionLt positionNe equal
      refine positionNe ?_
      have := (List.Nodup.getElem_inj_iff
        (pathContextList_nodup (k := k) firstNe)).mp
        (equal.trans selfSucc.symm)
      exact this
    rcases branch with rfl | rfl
    · refine (glueGraph_adj_iff _ _ _ _).mpr (Or.inr
        ⟨Sum.inr (ULift.up ⟨j, bound⟩),
          (pathContextList boundary first second k)[j]'(by
            rw [pathContextList_length]; omega), ?_, rfl, rfl⟩)
      refine (SimpleGraph.fromRel_adj _ _ _).mpr ⟨?_, ?_⟩
      · intro equal
        exact neighbourNe j (by rw [pathContextList_length]; omega)
          (by omega) equal.symm
      · refine Or.inr ⟨j, ?_, ?_⟩
        · exact List.getElem?_eq_getElem _
        · rw [List.getElem?_eq_getElem (by
            rw [pathContextList_length]; omega)]
          exact congrArg some selfSucc
    · refine (glueGraph_adj_iff _ _ _ _).mpr (Or.inr
        ⟨Sum.inr (ULift.up ⟨j, bound⟩),
          (pathContextList boundary first second k)[j + 2]'(by
            rw [pathContextList_length]; omega), ?_, rfl, rfl⟩)
      refine (SimpleGraph.fromRel_adj _ _ _).mpr ⟨?_, ?_⟩
      · intro equal
        exact neighbourNe (j + 2) (by rw [pathContextList_length]; omega)
          (by omega) equal.symm
      · refine Or.inl ⟨j + 1, ?_, ?_⟩
        · rw [List.getElem?_eq_getElem (by
            rw [pathContextList_length]; omega)]
          exact congrArg some selfSucc
        · exact List.getElem?_eq_getElem _

/-- With at least one internal chain vertex, every synthetic-chain relation
involves a chain vertex: the only non-chain positions are the two ends. -/
theorem pathContextRel_mem_chain (kPos : 1 ≤ k)
    {x y : boundary.Vertex ⊕ ULift.{u} (Fin k)}
    (related : PathContextRel boundary first second k x y) :
    (∃ index : ULift.{u} (Fin k), x = Sum.inr index) ∨
      ∃ index : ULift.{u} (Fin k), y = Sum.inr index := by
  obtain ⟨position, atPosition, atNext⟩ := related
  obtain ⟨positionLt, positionEq⟩ := List.getElem?_eq_some_iff.mp atPosition
  obtain ⟨nextLt, nextEq⟩ := List.getElem?_eq_some_iff.mp atNext
  rw [pathContextList_length] at positionLt nextLt
  by_cases positionChain : 1 ≤ position ∧ position ≤ k
  · left
    obtain ⟨j, jEq⟩ : ∃ j : Nat, position = j + 1 :=
      ⟨position - 1, by omega⟩
    subst jEq
    refine ⟨ULift.up ⟨j, by omega⟩, ?_⟩
    rw [← positionEq, pathContextList_getElem_succ (by omega)]
  · by_cases nextChain : 1 ≤ position + 1 ∧ position + 1 ≤ k
    · right
      refine ⟨ULift.up ⟨position, by omega⟩, ?_⟩
      rw [← nextEq, pathContextList_getElem_succ (by omega)]
    · -- both positions are ends: `position = 0` and `position + 1 = k + 1`,
      -- so `k = 0`, contradicting `1 ≤ k`
      exfalso
      omega

/-- **A glued walk avoiding the chain lifts to the atom side**: with `k ≥ 1`
the synthetic context owns no boundary–boundary edge, so every edge of a
chain-free walk is piece-owned. -/
theorem exists_pieceWalk_of_avoids_chain {piece : BoundaryPiece boundary}
    (kPos : 1 ≤ k) :
    ∀ {gluedStart gluedFinish :
        GluedVertex piece (pathContext boundary first second k)}
      (walk : (glue piece
        (pathContext boundary first second k)).graph.Walk gluedStart
          gluedFinish)
      {start finish : boundary.Vertex ⊕ piece.Internal}
      (_startEq : gluedStart =
        pieceEmbedding piece (pathContext boundary first second k) start)
      (_finishEq : gluedFinish =
        pieceEmbedding piece (pathContext boundary first second k) finish)
      (_avoids : ∀ vertex ∈ walk.support,
        ∀ index : ULift.{u} (Fin k), vertex ≠ Sum.inr (Sum.inr index)),
      ∃ lifted : piece.graph.Walk start finish,
        lifted.length = walk.length ∧
          walk.support = lifted.support.map
            (pieceEmbedding piece (pathContext boundary first second k)) ∧
          walk.edges = lifted.edges.map
            (Sym2.map (pieceEmbedding piece
              (pathContext boundary first second k))) := by
  intro gluedStart gluedFinish walk
  induction walk with
  | nil =>
      intro start finish startEq finishEq _avoids
      have startFinish : start = finish :=
        (pieceEmbedding piece (pathContext boundary first second k)).injective
          (startEq.symm.trans finishEq)
      subst startFinish
      refine ⟨SimpleGraph.Walk.nil, rfl,
        congrArg (fun vertex => [vertex]) startEq, rfl⟩
  | @cons head next tail adjacent rest ih =>
      intro start finish startEq finishEq avoids
      subst startEq
      -- the first edge is piece-owned
      rcases (glueGraph_adj_iff piece
          (pathContext boundary first second k) _ _).mp adjacent with
        ⟨pieceLeft, pieceRight, pieceAdj, leftEq, rightEq⟩ |
        ⟨contextLeft, contextRight, contextAdj, leftEq, rightEq⟩
      · have leftIsStart : pieceLeft = start :=
          (pieceEmbedding piece
            (pathContext boundary first second k)).injective leftEq
        subst leftIsStart
        obtain ⟨lifted, liftedLength, liftedSupport, liftedEdges⟩ :=
          ih rightEq.symm finishEq
            (fun vertex member index => avoids vertex
              (List.mem_cons_of_mem _ member) index)
        refine ⟨SimpleGraph.Walk.cons pieceAdj lifted, ?_, ?_, ?_⟩
        · show lifted.length + 1 = rest.length + 1
          rw [liftedLength]
          rfl
        · show _ :: rest.support =
            List.map (pieceEmbedding piece
              (pathContext boundary first second k)) (_ :: lifted.support)
          rw [List.map_cons, ← liftedSupport]
          rfl
        · show _ :: rest.edges =
            List.map (Sym2.map (pieceEmbedding piece
              (pathContext boundary first second k)))
              (s(pieceLeft, pieceRight) :: lifted.edges)
          rw [List.map_cons, ← liftedEdges]
          show s(_, next) :: rest.edges = _ :: rest.edges
          congr 1
          rw [Sym2.map_mk]
          exact (congrArg₂ (fun a b => s(a, b)) leftEq rightEq).symm
      · -- a context edge with `k ≥ 1` uses a chain vertex, which the walk
        -- avoids
        exfalso
        have related := (SimpleGraph.fromRel_adj _ _ _).mp contextAdj
        have chainSide := related.2
        rcases chainSide with direct | reversed
        · rcases pathContextRel_mem_chain kPos direct with
            ⟨index, chainEq⟩ | ⟨index, chainEq⟩
          · subst chainEq
            exact absurd leftEq.symm (by
              rcases start with label | inside <;>
                simp [pieceEmbedding, contextEmbedding])
          · subst chainEq
            refine avoids next
              (List.mem_cons_of_mem _ rest.start_mem_support) index
              rightEq.symm
        · rcases pathContextRel_mem_chain kPos reversed with
            ⟨index, chainEq⟩ | ⟨index, chainEq⟩
          · subst chainEq
            refine avoids next
              (List.mem_cons_of_mem _ rest.start_mem_support) index
              rightEq.symm
          · subst chainEq
            exact absurd leftEq.symm (by
              rcases start with label | inside <;>
                simp [pieceEmbedding, contextEmbedding])

/-- **The forced chain traversal**: a glued path from an internal chain vertex
to the far label that does not step back through its predecessor runs straight
up the chain — its length is exactly `k − j`, and its support consists of chain
vertices at or above `j` together with the far label. -/
theorem chain_walk_length {piece : BoundaryPiece boundary}
    (firstNe : first ≠ second) :
    ∀ (fuel : Nat) {j : Nat} (bound : j < k)
      (walk : (glue piece (pathContext boundary first second k)).graph.Walk
        (contextEmbedding piece (pathContext boundary first second k)
          (Sum.inr (ULift.up ⟨j, bound⟩)))
        (Sum.inl second))
      (walkPath : walk.IsPath)
      (noPred : contextEmbedding piece (pathContext boundary first second k)
          ((pathContextList boundary first second k)[j]'(by
            rw [pathContextList_length]; omega)) ∉ walk.support)
      (fuelEq : k - j = fuel + 1),
      walk.length = k - j ∧
        (∀ vertex ∈ walk.support,
          vertex = Sum.inl second ∨
            ∃ (i : Nat) (iBound : i < k), j ≤ i ∧
              vertex = contextEmbedding piece
                (pathContext boundary first second k)
                (Sum.inr (ULift.up ⟨i, iBound⟩))) ∧
        ∀ (i : Nat) (iBound : i < k), j ≤ i →
          contextEmbedding piece (pathContext boundary first second k)
              (Sum.inr (ULift.up ⟨i, iBound⟩)) ∈ walk.support := by
  intro fuel
  induction fuel with
  | zero =>
      intro j bound walk walkPath noPred fuelEq
      -- `j = k - 1`: the successor is the far label itself
      have jEq : j = k - 1 := by omega
      cases walk with
      | cons adjacent rest =>
          rename_i next
          have nextCases := (glue_adj_chain firstNe bound next).mp adjacent
          rcases nextCases with predEq | succEq
          · exfalso
            refine noPred ?_
            rw [← predEq]
            exact List.mem_cons_of_mem _ rest.start_mem_support
          · have lastEq : (pathContextList boundary first second k)[j + 2]'(by
                rw [pathContextList_length]; omega) = Sum.inl second := by
              have : j + 2 = k + 1 := by omega
              rw [← pathContextList_getElem_last (k := k)]
              congr 1
            rw [lastEq] at succEq
            have nextIsSecond : next = Sum.inl second := by
              simpa [contextEmbedding] using succEq
            subst nextIsSecond
            have restNil : rest = SimpleGraph.Walk.nil :=
              SimpleGraph.Walk.isPath_iff_eq_nil.mp
                ((SimpleGraph.Walk.cons_isPath_iff _ _).mp walkPath).1
            subst restNil
            refine ⟨fuelEq.symm, ?_, ?_⟩
            · intro vertex member
              rcases List.eq_or_mem_of_mem_cons member with headEq | tailMember
              · exact Or.inr ⟨j, bound, le_refl _, headEq⟩
              · left
                have retyped : vertex ∈ ([Sum.inl second] :
                    List (GluedVertex piece
                      (pathContext boundary first second k))) := tailMember
                exact List.mem_singleton.mp retyped
            · intro i iBound iGe
              have iEq : i = j := by omega
              subst iEq
              exact List.mem_cons_self
  | succ fuel ih =>
      intro j bound walk walkPath noPred fuelEq
      cases walk with
      | cons adjacent rest =>
          rename_i next
          have nextCases := (glue_adj_chain firstNe bound next).mp adjacent
          rcases nextCases with predEq | succEq
          · exfalso
            refine noPred ?_
            rw [← predEq]
            exact List.mem_cons_of_mem _ rest.start_mem_support
          · -- the successor is the next chain vertex
            have succBound : j + 1 < k := by omega
            have succAt : (pathContextList boundary first second k)[j + 2]'(by
                rw [pathContextList_length]; omega) =
                  Sum.inr (ULift.up ⟨j + 1, succBound⟩) := by
              rw [← pathContextList_getElem_succ (j := j + 1) succBound]
            rw [succAt] at succEq
            subst succEq
            have restPath :=
              ((SimpleGraph.Walk.cons_isPath_iff _ _).mp walkPath).1
            have headFresh :=
              ((SimpleGraph.Walk.cons_isPath_iff _ _).mp walkPath).2
            have predAt : (pathContextList boundary first second k)[j + 1]'(by
                rw [pathContextList_length]; omega) =
                  Sum.inr (ULift.up ⟨j, bound⟩) :=
              pathContextList_getElem_succ bound
            obtain ⟨restLength, restSupport, restCovers⟩ := ih succBound rest
              restPath
              (by
                rw [predAt]
                exact headFresh)
              (by omega)
            refine ⟨by
              show rest.length + 1 = k - j
              have bridge : rest.length = k - (j + 1) := restLength
              omega, ?_, ?_⟩
            · intro vertex member
              rcases List.eq_or_mem_of_mem_cons member with headEq | tailMember
              · exact Or.inr ⟨j, bound, le_refl _, headEq⟩
              · rcases restSupport vertex tailMember with secondEq | ⟨i, iBound,
                  iGe, chainEq⟩
                · exact Or.inl secondEq
                · exact Or.inr ⟨i, iBound, by omega, chainEq⟩
            · intro i iBound iGe
              by_cases iEq : i = j
              · subst iEq
                exact List.mem_cons_self
              · exact List.mem_cons_of_mem _
                  (restCovers i iBound (by omega))

/-- The two cycle-neighbours of a chain vertex are exactly its chain
predecessor and successor. -/
theorem cycle_neighbours_of_chain {piece : BoundaryPiece boundary}
    (firstNe : first ≠ second)
    {base : GluedVertex piece (pathContext boundary first second k)}
    {c : (glue piece (pathContext boundary first second k)).graph.Walk base
      base}
    (cycle : c.IsCycle) {j : Nat} (bound : j < k)
    (chainMem : contextEmbedding piece (pathContext boundary first second k)
        (Sum.inr (ULift.up ⟨j, bound⟩)) ∈ c.support) :
    contextEmbedding piece (pathContext boundary first second k)
        ((pathContextList boundary first second k)[j]'(by
          rw [pathContextList_length]; omega)) ∈ c.support ∧
      contextEmbedding piece (pathContext boundary first second k)
          ((pathContextList boundary first second k)[j + 2]'(by
            rw [pathContextList_length]; omega)) ∈ c.support := by
  letI : DecidableEq (GluedVertex piece
    (pathContext boundary first second k)) := Classical.decEq _
  letI : DecidableEq (glue piece
    (pathContext boundary first second k)).Vertex := Classical.decEq _
  set chainVertex := contextEmbedding piece
    (pathContext boundary first second k) (Sum.inr (ULift.up ⟨j, bound⟩))
    with chainVertexDef
  have rotatedCycle := cycle.rotate chainMem
  set rotated := c.rotate chainVertex chainMem with rotatedDef
  have rotatedNotNil : ¬ rotated.Nil := rotatedCycle.not_nil
  -- the two cycle-neighbours at the chain vertex
  have sndAdj := rotated.adj_snd rotatedNotNil
  have penAdj := rotated.adj_penultimate rotatedNotNil
  have sndPen : rotated.snd ≠ rotated.penultimate :=
    rotatedCycle.snd_ne_penultimate
  have sndMem : rotated.snd ∈ rotated.support := by
    rw [← SimpleGraph.Walk.cons_support_tail rotatedNotNil]
    exact List.mem_cons_of_mem _ rotated.tail.start_mem_support
  have penMem : rotated.penultimate ∈ rotated.support := by
    rw [← SimpleGraph.Walk.support_dropLast_concat rotatedNotNil]
    exact List.mem_append_left _ rotated.dropLast.end_mem_support
  have sndCases := (glue_adj_chain firstNe bound rotated.snd).mp sndAdj
  have penCases := (glue_adj_chain firstNe bound rotated.penultimate).mp
    penAdj.symm
  -- distinctness forces the pair to cover both chain neighbours
  have coverage :
      (contextEmbedding piece (pathContext boundary first second k)
          ((pathContextList boundary first second k)[j]'(by
            rw [pathContextList_length]; omega)) = rotated.snd ∨
        contextEmbedding piece (pathContext boundary first second k)
          ((pathContextList boundary first second k)[j]'(by
            rw [pathContextList_length]; omega)) = rotated.penultimate) ∧
      (contextEmbedding piece (pathContext boundary first second k)
          ((pathContextList boundary first second k)[j + 2]'(by
            rw [pathContextList_length]; omega)) = rotated.snd ∨
        contextEmbedding piece (pathContext boundary first second k)
          ((pathContextList boundary first second k)[j + 2]'(by
            rw [pathContextList_length]; omega)) = rotated.penultimate) := by
    rcases sndCases with sndPred | sndSucc
    · rcases penCases with penPred | penSucc
      · exact absurd (sndPred.trans penPred.symm) sndPen
      · exact ⟨Or.inl sndPred.symm, Or.inr penSucc.symm⟩
    · rcases penCases with penPred | penSucc
      · exact ⟨Or.inr penPred.symm, Or.inl sndSucc.symm⟩
      · exact absurd (sndSucc.trans penSucc.symm) sndPen
  have memTransfer : ∀ vertex : GluedVertex piece
      (pathContext boundary first second k),
      vertex = rotated.snd ∨ vertex = rotated.penultimate →
        vertex ∈ c.support := by
    intro vertex cases
    have inRotated : vertex ∈ rotated.support := by
      rcases cases with rfl | rfl
      · exact sndMem
      · exact penMem
    exact (SimpleGraph.Walk.mem_support_rotate_iff c chainVertex
      chainMem).mp inRotated
  exact ⟨memTransfer _ coverage.1, memTransfer _ coverage.2⟩

/-- Downward propagation: a chain vertex on a cycle forces the first label
onto the cycle. -/
theorem first_label_mem_of_chain_mem {piece : BoundaryPiece boundary}
    (firstNe : first ≠ second)
    {base : GluedVertex piece (pathContext boundary first second k)}
    {c : (glue piece (pathContext boundary first second k)).graph.Walk base
      base}
    (cycle : c.IsCycle) :
    ∀ (j : Nat) (bound : j < k),
      contextEmbedding piece (pathContext boundary first second k)
          (Sum.inr (ULift.up ⟨j, bound⟩)) ∈ c.support →
      (Sum.inl first : GluedVertex piece
        (pathContext boundary first second k)) ∈ c.support := by
  intro j
  induction j with
  | zero =>
      intro bound chainMem
      have pred := (cycle_neighbours_of_chain firstNe cycle bound chainMem).1
      rw [pathContextList_getElem_zero] at pred
      exact pred
  | succ i ihDown =>
      intro bound chainMem
      have pred := (cycle_neighbours_of_chain firstNe cycle bound chainMem).1
      have predEq : (pathContextList boundary first second k)[i + 1]'(by
          rw [pathContextList_length]; omega) =
            Sum.inr (ULift.up ⟨i, by omega⟩) :=
        pathContextList_getElem_succ (by omega)
      rw [predEq] at pred
      exact ihDown (by omega) pred

/-- Upward propagation: a chain vertex on a cycle forces the second label
onto the cycle. -/
theorem second_label_mem_of_chain_mem {piece : BoundaryPiece boundary}
    (firstNe : first ≠ second)
    {base : GluedVertex piece (pathContext boundary first second k)}
    {c : (glue piece (pathContext boundary first second k)).graph.Walk base
      base}
    (cycle : c.IsCycle) :
    ∀ (fuel j : Nat) (bound : j < k), k - j = fuel + 1 →
      contextEmbedding piece (pathContext boundary first second k)
          (Sum.inr (ULift.up ⟨j, bound⟩)) ∈ c.support →
      (Sum.inl second : GluedVertex piece
        (pathContext boundary first second k)) ∈ c.support := by
  intro fuel
  induction fuel with
  | zero =>
      intro j bound fuelEq chainMem
      have succ := (cycle_neighbours_of_chain firstNe cycle bound chainMem).2
      have succEq : (pathContextList boundary first second k)[j + 2]'(by
          rw [pathContextList_length]; omega) = Sum.inl second := by
        rw [← pathContextList_getElem_last (k := k) (boundary := boundary)
          (first := first) (second := second)]
        all_goals first
          | rfl
          | (congr 1 <;> omega)
      rw [succEq] at succ
      exact succ
  | succ fuel ihUp =>
      intro j bound fuelEq chainMem
      have succ := (cycle_neighbours_of_chain firstNe cycle bound chainMem).2
      have succBound : j + 1 < k := by omega
      have succEq : (pathContextList boundary first second k)[j + 2]'(by
          rw [pathContextList_length]; omega) =
            Sum.inr (ULift.up ⟨j + 1, succBound⟩) := by
        rw [← pathContextList_getElem_succ succBound]
        all_goals first
          | rfl
          | (congr 1 <;> omega)
      rw [succEq] at succ
      exact ihUp (j + 1) succBound (by omega) succ

/-- Downward propagation to the bottom chain vertex. -/
theorem chain_zero_mem_of_chain_mem {piece : BoundaryPiece boundary}
    (firstNe : first ≠ second)
    {base : GluedVertex piece (pathContext boundary first second k)}
    {c : (glue piece (pathContext boundary first second k)).graph.Walk base
      base}
    (cycle : c.IsCycle) :
    ∀ (j : Nat) (bound : j < k),
      contextEmbedding piece (pathContext boundary first second k)
          (Sum.inr (ULift.up ⟨j, bound⟩)) ∈ c.support →
      contextEmbedding piece (pathContext boundary first second k)
          (Sum.inr (ULift.up ⟨0, by omega⟩)) ∈ c.support := by
  intro j
  induction j with
  | zero =>
      intro bound chainMem
      exact chainMem
  | succ i ihDown =>
      intro bound chainMem
      have pred := (cycle_neighbours_of_chain firstNe cycle bound chainMem).1
      have predEq : (pathContextList boundary first second k)[i + 1]'(by
          rw [pathContextList_length]; omega) =
            Sum.inr (ULift.up ⟨i, by omega⟩) :=
        pathContextList_getElem_succ (by omega)
      rw [predEq] at pred
      exact ihDown (by omega) pred

/-- **A chain vertex on a cycle propagates to both endpoint labels.** -/
theorem endpoint_labels_mem_of_chain_mem {piece : BoundaryPiece boundary}
    (firstNe : first ≠ second)
    {base : GluedVertex piece (pathContext boundary first second k)}
    {c : (glue piece (pathContext boundary first second k)).graph.Walk base
      base}
    (cycle : c.IsCycle) {j : Nat} (bound : j < k)
    (chainMem : contextEmbedding piece (pathContext boundary first second k)
        (Sum.inr (ULift.up ⟨j, bound⟩)) ∈ c.support) :
    (Sum.inl first : GluedVertex piece
        (pathContext boundary first second k)) ∈ c.support ∧
      (Sum.inl second : GluedVertex piece
        (pathContext boundary first second k)) ∈ c.support :=
  ⟨first_label_mem_of_chain_mem firstNe cycle j bound chainMem,
    second_label_mem_of_chain_mem firstNe cycle (k - j - 1) j bound
      (by omega) chainMem⟩

/-- **The chain-carrying arc is the port path itself**: a glued path from the
first label to the second label through the bottom chain vertex consists of
one crossing edge and the full forced chain — its length is `k + 1` and it
covers every chain vertex. -/
theorem chainArc_of_path {piece : BoundaryPiece boundary}
    (firstNe : first ≠ second) (kPos : 1 ≤ k)
    {p : (glue piece (pathContext boundary first second k)).graph.Walk
      (Sum.inl first) (Sum.inl second)}
    (pPath : p.IsPath)
    (chainZero : contextEmbedding piece (pathContext boundary first second k)
        (Sum.inr (ULift.up ⟨0, by omega⟩)) ∈ p.support) :
    p.length = k + 1 ∧
      ∀ (i : Nat) (iBound : i < k),
        contextEmbedding piece (pathContext boundary first second k)
            (Sum.inr (ULift.up ⟨i, iBound⟩)) ∈ p.support := by
  classical
  have zeroBound : (0 : Nat) < k := by omega
  have spec := SimpleGraph.Walk.take_spec p chainZero
  set q1 := p.takeUntil _ chainZero with q1Def
  set q2 := p.dropUntil _ chainZero with q2Def
  have q1Path : q1.IsPath := pPath.takeUntil chainZero
  have q2Path : q2.IsPath := pPath.dropUntil chainZero
  have supportSplit : p.support = q1.support ++ q2.support.tail := by
    conv_lhs => rw [← spec]
    exact SimpleGraph.Walk.support_append q1 q2
  have pNodup := pPath.support_nodup
  rw [supportSplit] at pNodup
  obtain ⟨_, _, disjointParts⟩ := List.nodup_append.mp pNodup
  have chainZeroNeA : (Sum.inl first : GluedVertex piece
      (pathContext boundary first second k)) ≠
        contextEmbedding piece (pathContext boundary first second k)
          (Sum.inr (ULift.up ⟨0, by omega⟩)) := by
    intro h
    have h' : (Sum.inl first : GluedVertex piece
        (pathContext boundary first second k)) =
          Sum.inr (Sum.inr (ULift.up ⟨0, by omega⟩)) := h
    cases h'
  have q2NotNil : ¬ q2.Nil := by
    refine SimpleGraph.Walk.not_nil_of_ne ?_
    intro h
    have h' : (Sum.inr (Sum.inr (ULift.up ⟨0, by omega⟩)) :
        GluedVertex piece (pathContext boundary first second k)) =
          Sum.inl second := h
    cases h'
  have q1NotNil : ¬ q1.Nil := SimpleGraph.Walk.not_nil_of_ne chainZeroNeA
  -- the first label avoids the dropped arc
  have ANotQ2 : (Sum.inl first : GluedVertex piece
      (pathContext boundary first second k)) ∉ q2.support := by
    intro AMem
    rw [← SimpleGraph.Walk.cons_support_tail q2NotNil] at AMem
    rcases List.eq_or_mem_of_mem_cons AMem with h | h
    · exact chainZeroNeA h
    · -- A also heads q1
      have tailEq : q2.support.tail = q2.tail.support := by
        conv_lhs => rw [← SimpleGraph.Walk.cons_support_tail q2NotNil]
        rfl
      exact (disjointParts _ q1.start_mem_support _
        (by rw [tailEq]; exact h)) rfl
  -- the dropped arc is the forced chain
  have noPred : contextEmbedding piece (pathContext boundary first second k)
      ((pathContextList boundary first second k)[0]'(by
        rw [pathContextList_length]; omega)) ∉ q2.support := by
    rw [pathContextList_getElem_zero]
    exact ANotQ2
  obtain ⟨q2Len, _q2Sup, q2Cov⟩ := chain_walk_length firstNe (k - 1)
    zeroBound q2 q2Path noPred (by omega)
  -- the taken arc is a single crossing edge
  have penAdj := q1.adj_penultimate q1NotNil
  have penCases := (glue_adj_chain firstNe zeroBound q1.penultimate).mp
    penAdj.symm
  have sndAdj := q2.adj_snd q2NotNil
  have sndCases := (glue_adj_chain firstNe zeroBound q2.snd).mp sndAdj
  have sndMem : q2.snd ∈ q2.support := by
    rw [← SimpleGraph.Walk.cons_support_tail q2NotNil]
    exact List.mem_cons_of_mem _ q2.tail.start_mem_support
  have sndUpper : q2.snd = contextEmbedding piece
      (pathContext boundary first second k)
        ((pathContextList boundary first second k)[2]'(by
          rw [pathContextList_length]; omega)) := by
    rcases sndCases with sPred | sSucc
    · exfalso
      rw [pathContextList_getElem_zero] at sPred
      have sPred' : q2.snd = Sum.inl first := sPred
      rw [sPred'] at sndMem
      exact ANotQ2 sndMem
    · exact sSucc
  have penEq : q1.penultimate = (Sum.inl first : GluedVertex piece
      (pathContext boundary first second k)) := by
    rcases penCases with pPred | pSucc
    · rw [pathContextList_getElem_zero] at pPred
      exact pPred
    · exfalso
      have penMem : q1.penultimate ∈ q1.support := by
        rw [← SimpleGraph.Walk.support_dropLast_concat q1NotNil]
        exact List.mem_append_left _ q1.dropLast.end_mem_support
      have sndTail : q2.snd ∈ q2.support.tail := by
        have tailEq : q2.support.tail = q2.tail.support := by
          conv_lhs => rw [← SimpleGraph.Walk.cons_support_tail q2NotNil]
          rfl
        rw [tailEq]
        exact q2.tail.start_mem_support
      rw [pSucc.trans sndUpper.symm] at penMem
      exact (disjointParts _ penMem _ sndTail) rfl
  -- a path revisiting its start has length one here
  have lenPos : q1.length ≠ 0 := by
    intro zero
    exact q1NotNil (SimpleGraph.Walk.length_eq_zero_iff.mp zero)
  have lenOne : q1.length = 1 := by
    have injOn := q1Path.getVert_injOn
    have penGet : q1.getVert (q1.length - 1) = Sum.inl first := penEq
    have zeroGet : q1.getVert 0 = Sum.inl first :=
      SimpleGraph.Walk.getVert_zero q1
    have posEq : q1.length - 1 = 0 :=
      injOn (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega)
        (penGet.trans zeroGet.symm)
    omega
  -- length assembly
  have pLen : p.length = k + 1 := by
    have lengths := congrArg SimpleGraph.Walk.length spec
    rw [SimpleGraph.Walk.length_append] at lengths
    have bridge2 : q2.length = k - 0 := q2Len
    omega
  refine ⟨pLen, ?_⟩
  intro i iBound
  by_cases iZero : i = 0
  · subst iZero
    exact chainZero
  · have inQ2 := q2Cov i iBound (by omega)
    rw [supportSplit]
    refine List.mem_append_right _ ?_
    rw [← SimpleGraph.Walk.cons_support_tail q2NotNil] at inQ2
    rcases List.eq_or_mem_of_mem_cons inQ2 with h | h
    · exfalso
      have h' : (Sum.inr (Sum.inr (ULift.up ⟨i, iBound⟩)) :
          GluedVertex piece (pathContext boundary first second k)) =
            Sum.inr (Sum.inr (ULift.up ⟨0, by omega⟩)) := h
      have := congrArg (fun v => match v with
        | Sum.inr (Sum.inr index) => index.down.1
        | _ => 0) h'
      simp at this
      exact iZero this
    · have tailEq : q2.support.tail = q2.tail.support := by
        conv_lhs => rw [← SimpleGraph.Walk.cons_support_tail q2NotNil]
        rfl
      rw [tailEq]
      exact h

/-- **A chain-free cycle of the gluing lifts to a cycle of the atom side.** -/
theorem exists_pieceCycle_of_avoids_chain {piece : BoundaryPiece boundary}
    (kPos : 1 ≤ k)
    {base : GluedVertex piece (pathContext boundary first second k)}
    {c : (glue piece (pathContext boundary first second k)).graph.Walk base
      base}
    (cycle : c.IsCycle)
    (avoids : ∀ vertex ∈ c.support, ∀ index : ULift.{u} (Fin k),
      vertex ≠ Sum.inr (Sum.inr index)) :
    ∃ (pieceBase : boundary.Vertex ⊕ piece.Internal)
      (lifted : piece.graph.Walk pieceBase pieceBase),
        lifted.IsCycle ∧ lifted.length = c.length := by
  classical
  obtain ⟨pieceBase, baseEq⟩ : ∃ pieceBase : boundary.Vertex ⊕ piece.Internal,
      base = pieceEmbedding piece (pathContext boundary first second k)
        pieceBase := by
    rcases base with label | inner
    · exact ⟨.inl label, rfl⟩
    · rcases inner with pieceInner | chainInner
      · exact ⟨.inr pieceInner, rfl⟩
      · exact absurd rfl (avoids _ c.start_mem_support chainInner)
  obtain ⟨lifted, liftedLength, liftedSupport, liftedEdges⟩ :=
    exists_pieceWalk_of_avoids_chain kPos c baseEq baseEq avoids
  obtain ⟨cTrail, _cNeNil, cTailNodup⟩ :=
    (SimpleGraph.Walk.isCycle_def c).mp cycle
  refine ⟨pieceBase, lifted, ?_, liftedLength⟩
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isTrail_def]
    have cEdgesNodup : c.edges.Nodup :=
      (SimpleGraph.Walk.isTrail_def c).mp cTrail
    rw [liftedEdges] at cEdgesNodup
    exact cEdgesNodup.of_map
  · intro liftedNil
    have liftedZero : lifted.length = 0 := by
      rw [liftedNil]
      rfl
    have cZero : c.length = 0 := by
      rw [← liftedLength, liftedZero]
    exact cycle.not_nil (SimpleGraph.Walk.length_eq_zero_iff.mp cZero)
  · have tailEq : c.support.tail = lifted.support.tail.map
        (pieceEmbedding piece (pathContext boundary first second k)) := by
      rw [liftedSupport]
      simp only [List.map_tail]
      rfl
    rw [tailEq] at cTailNodup
    exact cTailNodup.of_map

/-- **The classification of cycles in a synthetic-context gluing**: every
cycle either avoids the chain — and lifts to a cycle of the atom side — or
crosses it, and then it consists of the full port path together with a
piece-side path between the two labels of complementary length. -/
theorem cycle_classify {piece : BoundaryPiece boundary}
    (firstNe : first ≠ second) (kPos : 1 ≤ k)
    {base : GluedVertex piece (pathContext boundary first second k)}
    {c : (glue piece (pathContext boundary first second k)).graph.Walk base
      base}
    (cycle : c.IsCycle) :
    (∃ (pieceBase : boundary.Vertex ⊕ piece.Internal)
      (lifted : piece.graph.Walk pieceBase pieceBase),
        lifted.IsCycle ∧ lifted.length = c.length) ∨
      ∃ q : piece.graph.Walk (.inl second) (.inl first),
        q.IsPath ∧ q.length + (k + 1) = c.length := by
  classical
  letI : DecidableEq (GluedVertex piece
    (pathContext boundary first second k)) := Classical.decEq _
  by_cases chainMeet : ∃ (i : Nat) (iBound : i < k),
      contextEmbedding piece (pathContext boundary first second k)
        (Sum.inr (ULift.up ⟨i, iBound⟩)) ∈ c.support
  · -- the crossing case
    obtain ⟨j, bound, chainMem⟩ := chainMeet
    right
    have firstMem : (Sum.inl first : GluedVertex piece
        (pathContext boundary first second k)) ∈ c.support :=
      first_label_mem_of_chain_mem firstNe cycle j bound chainMem
    have secondMem : (Sum.inl second : GluedVertex piece
        (pathContext boundary first second k)) ∈ c.support :=
      second_label_mem_of_chain_mem firstNe cycle (k - j - 1) j bound
        (by omega) chainMem
    have chainZeroMem := chain_zero_mem_of_chain_mem firstNe cycle j bound
      chainMem
    -- rotate to the first label and split at the second
    have cycleA : (c.rotate (Sum.inl first) firstMem).IsCycle :=
      cycle.rotate firstMem
    set cA := c.rotate (Sum.inl first) firstMem with cADef
    have secondMemA : (Sum.inl second : GluedVertex piece
        (pathContext boundary first second k)) ∈ cA.support :=
      (SimpleGraph.Walk.mem_support_rotate_iff c _ firstMem).mpr secondMem
    have chainZeroMemA : contextEmbedding piece
        (pathContext boundary first second k)
          (Sum.inr (ULift.up ⟨0, by omega⟩)) ∈ cA.support :=
      (SimpleGraph.Walk.mem_support_rotate_iff c _ firstMem).mpr chainZeroMem
    have spec := SimpleGraph.Walk.take_spec cA secondMemA
    set p1 := cA.takeUntil _ secondMemA with p1Def
    set p2 := cA.dropUntil _ secondMemA with p2Def
    have ABne : (Sum.inl first : GluedVertex piece
        (pathContext boundary first second k)) ≠ Sum.inl second := by
      intro h
      exact firstNe (by simpa using h)
    have p1Path : p1.IsPath := cycleA.isPath_takeUntil secondMemA
    have p1NotNil : ¬ p1.Nil := SimpleGraph.Walk.not_nil_of_ne ABne
    have p2NotNil : ¬ p2.Nil := SimpleGraph.Walk.not_nil_of_ne ABne.symm
    have p2Path : p2.IsPath := by
      refine SimpleGraph.Walk.IsCycle.isPath_of_append_right p1NotNil ?_
      rw [spec]
      exact cycleA
    have supportSplit : cA.support = p1.support ++ p2.support.tail := by
      conv_lhs => rw [← spec]
      exact SimpleGraph.Walk.support_append p1 p2
    have lengthSplit : p1.length + p2.length = c.length := by
      have lengths := congrArg SimpleGraph.Walk.length spec
      rw [SimpleGraph.Walk.length_append] at lengths
      rw [lengths]
      exact SimpleGraph.Walk.length_rotate c _ firstMem
    have p2TailEq : p2.support.tail = p2.tail.support := by
      conv_lhs => rw [← SimpleGraph.Walk.cons_support_tail p2NotNil]
      rfl
    -- the arc carrying the bottom chain vertex
    have chainZeroSplit : contextEmbedding piece
        (pathContext boundary first second k)
          (Sum.inr (ULift.up ⟨0, by omega⟩)) ∈ p1.support ∨
        contextEmbedding piece (pathContext boundary first second k)
          (Sum.inr (ULift.up ⟨0, by omega⟩)) ∈ p2.support.tail := by
      rw [supportSplit] at chainZeroMemA
      exact List.mem_append.mp chainZeroMemA
    -- a chain vertex sits on exactly one side: the cycle's tail is nodup
    have p1TailEq : p1.support.tail = p1.tail.support := by
      conv_lhs => rw [← SimpleGraph.Walk.cons_support_tail p1NotNil]
      rfl
    have splitTail : cA.support.tail =
        p1.tail.support ++ p2.support.tail := by
      rw [supportSplit]
      conv_lhs => rw [← SimpleGraph.Walk.cons_support_tail p1NotNil]
      rfl
    have tailNodup := ((SimpleGraph.Walk.isCycle_def cA).mp cycleA).2.2
    rw [splitTail] at tailNodup
    obtain ⟨_, _, pairNe⟩ := List.nodup_append.mp tailNodup
    have oneSide : ∀ (i : Nat) (iBound : i < k),
        contextEmbedding piece (pathContext boundary first second k)
            (Sum.inr (ULift.up ⟨i, iBound⟩)) ∈ p1.support →
          contextEmbedding piece (pathContext boundary first second k)
              (Sum.inr (ULift.up ⟨i, iBound⟩)) ∉ p2.support := by
      intro i iBound inP1 inP2
      have chainNeBase : contextEmbedding piece
          (pathContext boundary first second k)
            (Sum.inr (ULift.up ⟨i, iBound⟩)) ≠ Sum.inl first := by
        intro h
        cases (show (Sum.inr (Sum.inr (ULift.up ⟨i, iBound⟩)) :
          GluedVertex piece (pathContext boundary first second k)) =
            Sum.inl first from h)
      have chainNeSecond : contextEmbedding piece
          (pathContext boundary first second k)
            (Sum.inr (ULift.up ⟨i, iBound⟩)) ≠ Sum.inl second := by
        intro h
        cases (show (Sum.inr (Sum.inr (ULift.up ⟨i, iBound⟩)) :
          GluedVertex piece (pathContext boundary first second k)) =
            Sum.inl second from h)
      have inP1Tail : contextEmbedding piece
          (pathContext boundary first second k)
            (Sum.inr (ULift.up ⟨i, iBound⟩)) ∈ p1.tail.support := by
        rw [← SimpleGraph.Walk.cons_support_tail p1NotNil] at inP1
        rcases List.eq_or_mem_of_mem_cons inP1 with h | h
        · exact absurd h chainNeBase
        · exact h
      have inP2Tail : contextEmbedding piece
          (pathContext boundary first second k)
            (Sum.inr (ULift.up ⟨i, iBound⟩)) ∈ p2.support.tail := by
        rw [← SimpleGraph.Walk.cons_support_tail p2NotNil] at inP2
        rcases List.eq_or_mem_of_mem_cons inP2 with h | h
        · exact absurd h chainNeSecond
        · rw [p2TailEq]
          exact h
      exact (pairNe _ inP1Tail _ inP2Tail) rfl
    rcases chainZeroSplit with inP1 | inP2tail
    · -- the taken arc is the port path; the dropped arc lifts
      obtain ⟨p1Len, p1Covers⟩ := chainArc_of_path firstNe kPos p1Path inP1
      have p2Avoids : ∀ vertex ∈ p2.support,
          ∀ index : ULift.{u} (Fin k), vertex ≠ Sum.inr (Sum.inr index) := by
        rintro vertex member index rfl
        exact oneSide index.down.1 index.down.2
          (p1Covers index.down.1 index.down.2)
          (show contextEmbedding piece
              (pathContext boundary first second k)
              (Sum.inr (ULift.up ⟨index.down.1, index.down.2⟩)) ∈
            p2.support from member)
      obtain ⟨q, qLen, qSupport, _qEdges⟩ :=
        exists_pieceWalk_of_avoids_chain kPos p2
          (start := Sum.inl second) (finish := Sum.inl first) rfl rfl p2Avoids
      refine ⟨q, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_def]
        have := p2Path.support_nodup
        rw [qSupport] at this
        exact this.of_map
      · omega
    · -- the dropped arc is the port path; the taken arc lifts (reversed)
      have chainZeroP2Plain : contextEmbedding piece
          (pathContext boundary first second k)
            (Sum.inr (ULift.up ⟨0, by omega⟩)) ∈ p2.support := by
        rw [← SimpleGraph.Walk.cons_support_tail p2NotNil]
        exact List.mem_cons_of_mem _ (by rwa [← p2TailEq])
      have chainZeroP2 : contextEmbedding piece
          (pathContext boundary first second k)
            (Sum.inr (ULift.up ⟨0, by omega⟩)) ∈ p2.reverse.support := by
        rw [SimpleGraph.Walk.support_reverse]
        exact List.mem_reverse.mpr chainZeroP2Plain
      have p2RevPath : p2.reverse.IsPath :=
        (SimpleGraph.Walk.isPath_reverse_iff p2).mpr p2Path
      obtain ⟨p2Len, p2Covers⟩ := chainArc_of_path firstNe kPos p2RevPath
        chainZeroP2
      have p1Avoids : ∀ vertex ∈ p1.reverse.support,
          ∀ index : ULift.{u} (Fin k), vertex ≠ Sum.inr (Sum.inr index) := by
        rintro vertex member index rfl
        rw [SimpleGraph.Walk.support_reverse] at member
        have member' := List.mem_reverse.mp member
        refine oneSide index.down.1 index.down.2
          (show contextEmbedding piece
              (pathContext boundary first second k)
              (Sum.inr (ULift.up ⟨index.down.1, index.down.2⟩)) ∈
            p1.support from member') ?_
        have inRev := p2Covers index.down.1 index.down.2
        rw [SimpleGraph.Walk.support_reverse] at inRev
        exact List.mem_reverse.mp inRev
      obtain ⟨q, qLen, qSupport, _qEdges⟩ :=
        exists_pieceWalk_of_avoids_chain kPos p1.reverse
          (start := Sum.inl second) (finish := Sum.inl first) rfl rfl p1Avoids
      refine ⟨q, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_def]
        have := ((SimpleGraph.Walk.isPath_reverse_iff p1).mpr
          p1Path).support_nodup
        rw [qSupport] at this
        exact this.of_map
      · have p2LenPlain : p2.length = k + 1 := by
          rw [← SimpleGraph.Walk.length_reverse p2]
          exact p2Len
        have qLen' : q.length = p1.length := by
          rw [qLen, SimpleGraph.Walk.length_reverse]
        omega
  · -- the chain-free case
    left
    push_neg at chainMeet
    refine exists_pieceCycle_of_avoids_chain kPos cycle ?_
    rintro vertex member index rfl
    exact absurd member (chainMeet index.down.1 index.down.2)

/-- **The synthetic-context evaluation of the cycle target**: the glued
reading realizes the target exactly when the atom side carries an accepted
cycle of its own, or a piece path between the two labels closes an accepted
crossing cycle with the synthetic port path. -/
theorem hasCycleWithLength_glue_pathContext_iff {piece : BoundaryPiece boundary}
    (firstNe : first ≠ second) (kPos : 1 ≤ k) {LengthOK : Nat → Prop} :
    HasCycleWithLength LengthOK
        (glue piece (pathContext boundary first second k)) ↔
      ((∃ (pieceBase : boundary.Vertex ⊕ piece.Internal)
          (lifted : piece.graph.Walk pieceBase pieceBase),
            lifted.IsCycle ∧ LengthOK lifted.length) ∨
        ∃ q : piece.graph.Walk (.inl first) (.inl second),
          q.IsPath ∧ LengthOK (q.length + (k + 1))) := by
  constructor
  · rintro ⟨certificate⟩
    rcases cycle_classify firstNe kPos certificate.isCycle with
      ⟨pieceBase, lifted, liftedCycle, liftedLength⟩ | ⟨q, qPath, qLength⟩
    · refine Or.inl ⟨pieceBase, lifted, liftedCycle, ?_⟩
      rw [liftedLength]
      exact certificate.length_ok
    · refine Or.inr ⟨q.reverse, (SimpleGraph.Walk.isPath_reverse_iff q).mpr
        qPath, ?_⟩
      rw [SimpleGraph.Walk.length_reverse, qLength]
      exact certificate.length_ok
  · rintro (⟨pieceBase, lifted, liftedCycle, lengthOk⟩ | ⟨q, qPath, lengthOk⟩)
    · refine ⟨⟨_, lifted.map (pieceHom piece
        (pathContext boundary first second k)), ?_, ?_⟩⟩
      · exact liftedCycle.map (pieceEmbedding piece
          (pathContext boundary first second k)).injective
      · rw [SimpleGraph.Walk.length_map]
        exact lengthOk
    · exact hasCycleWithLength_glue_pathContext firstNe kPos q qPath lengthOk

/-- **The synthetic path context distinguishes two readings** whenever one
glued evaluation accepts and the other refuses. -/
theorem targetDefect_of_pathContext {left right : BoundaryPiece boundary}
    {LengthOK : Nat → Prop} (k : Nat)
    (accepts : HasCycleWithLength LengthOK
      (glue left (pathContext boundary first second k)))
    (refuses : ¬ HasCycleWithLength LengthOK
      (glue right (pathContext boundary first second k))) :
    Response.TargetDefect (HasCycleWithLength LengthOK) left right :=
  ⟨pathContext boundary first second k,
    fun same => refuses (same.mp accepts)⟩

/-- **The spectral separation form of the defect**: a piece path of accepted
complementary length on the left, no internal accepted cycle and no accepted
complementary path on the right. -/
theorem targetDefect_of_spectra {left right : BoundaryPiece boundary}
    (firstNe : first ≠ second) {LengthOK : Nat → Prop} {k : Nat}
    (kPos : 1 ≤ k)
    (leftPath : ∃ q : left.graph.Walk (.inl first) (.inl second),
      q.IsPath ∧ LengthOK (q.length + (k + 1)))
    (rightSafe : ¬ ∃ (pieceBase : boundary.Vertex ⊕ right.Internal)
      (lifted : right.graph.Walk pieceBase pieceBase),
        lifted.IsCycle ∧ LengthOK lifted.length)
    (rightSpectrum : ¬ ∃ q : right.graph.Walk (.inl first) (.inl second),
      q.IsPath ∧ LengthOK (q.length + (k + 1))) :
    Response.TargetDefect (HasCycleWithLength LengthOK) left right := by
  refine targetDefect_of_pathContext (first := first) (second := second)
    k ?_ ?_
  · exact (hasCycleWithLength_glue_pathContext_iff firstNe kPos).mpr
      (Or.inr leftPath)
  · intro target
    rcases (hasCycleWithLength_glue_pathContext_iff firstNe
        kPos).mp target with internal | spectral
    · exact rightSafe internal
    · exact rightSpectrum spectral

end PathContext

end Hypostructure.Graph
