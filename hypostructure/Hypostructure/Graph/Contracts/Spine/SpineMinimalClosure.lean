import Hypostructure.Graph.Statements.Spine

/-!
# Contracts: minimal-closure consequences of the selection

Proof-agnostic contract lemmas for the two structural closure facts read off
the selection's minimality: the two-terminal gadget closure and contraction
criticality.  Each lemma is stated over a `Graph.FiniteObject` with the
registered `Parameters` as a parameter and every hypothesis explicit; its
conclusion is exactly the statement of the fact it proves.  This module imports
no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u v

/-- **Two-terminal closure** (no manuscript label).  On a selected object
(`SelectionStatement`) at the cubic baseline (`CubicBaselineStatement`), with
the accepted lengths exactly the powers of two, every strictly smaller
two-terminal closure, added-edge closure, doubled closure, and complement
closure carries a terminal path of accepted length. -/
theorem gadgetClosure_of_selection
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation}
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (selection : SelectionStatement BranchState Presentation presentation data object)
    (cubicBaseline : CubicBaselineStatement data)
    (lengthOK_iff_powerOfTwo : ∀ length,
      data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    GadgetClosureStatement data object := by
  have cubic := cubicBaseline.1
  classical
  dsimp only [GadgetClosureStatement]
  let avoids (piece : Graph.FiniteObject.{u}) :=
    ¬ Graph.HasCycleWithLength data.LengthOK piece
  let cubicPiece (piece : Graph.FiniteObject.{u}) (x y : piece.Vertex) :=
    x ≠ y ∧ piece.degree x = 2 ∧ piece.degree y = 2 ∧
      ∀ vertex, vertex ≠ x → vertex ≠ y → piece.degree vertex = 3
  have minimal : ∀ candidate : Graph.FiniteObject.{u},
      candidate.LexicographicallySmaller object →
      3 ≤ candidate.minDegree →
      Graph.HasCycleWithLength data.LengthOK candidate := by
    intro candidate smaller baseline
    apply selection.2.sizeMinimal candidate smaller
    rw [cubic]
    exact baseline
  have accepted (length : Nat) : data.LengthOK length ↔
      Core.DyadicLength.PowerOfTwoLength length :=
    lengthOK_iff_powerOfTwo length
  constructor
  · intro left right a b c d leftCubic rightCubic leftAvoids rightAvoids
      count baseline
    have smaller :
        (Graph.TwoTerminalClosure.close left right a b c d).LexicographicallySmaller
          object :=
      Graph.FiniteObject.lexicographicallySmaller_of_vertexCount_lt (by
        rw [Graph.TwoTerminalClosure.vertexCount_close]
        exact count)
    obtain ⟨leftPath, rightPath, leftIsPath, rightIsPath, lengthOK⟩ :=
      Graph.TwoTerminalClosure.terminal_paths_of_minimal_closure
        object left right a b c d leftCubic.1 rightCubic.1
        leftAvoids rightAvoids smaller baseline minimal
    exact ⟨leftPath, rightPath, leftIsPath, rightIsPath,
      (accepted _).mp lengthOK⟩
  · constructor
    · intro piece a b count pieceCubic pieceAvoids baseline
      have smaller : (piece.addEdge a b).LexicographicallySmaller
          object :=
        Graph.FiniteObject.lexicographicallySmaller_of_vertexCount_lt (by
          simpa using count)
      obtain ⟨path, pathIsPath, lengthOK⟩ :=
        Graph.AddedEdgeClosure.terminalPath_of_minimal_addedEdge
          object piece a b pieceCubic.1 pieceAvoids smaller
          baseline minimal
      obtain ⟨exponent, exponentLower, equality⟩ :=
        (Core.DyadicLength.powerOfTwoLength_iff _).mp
          ((accepted _).mp lengthOK)
      exact ⟨path, exponent, pathIsPath, by omega, by omega⟩
    · constructor
      · intro piece a b count pieceCubic pieceAvoids baseline
        have smaller :
            (Graph.TwoTerminalClosure.close piece piece a b a b).LexicographicallySmaller
              object :=
          Graph.FiniteObject.lexicographicallySmaller_of_vertexCount_lt (by
            rw [Graph.TwoTerminalClosure.vertexCount_close]
            simpa [two_mul] using count)
        obtain ⟨first, second, firstPath, secondPath, lengthOK⟩ :=
          Graph.TwoTerminalClosure.terminal_paths_of_minimal_closure
            object piece piece a b a b pieceCubic.1 pieceCubic.1
            pieceAvoids pieceAvoids smaller baseline minimal
        obtain ⟨exponent, _lower, equality⟩ :=
          (Core.DyadicLength.powerOfTwoLength_iff _).mp
            ((accepted _).mp lengthOK)
        exact ⟨first, second, exponent, firstPath, secondPath, by omega⟩
      · intro support complementSupport
        dsimp
        intro t1 t2 u1 u2 _isComplement _pieceCubic _pieceAvoids complementAvoids
          different _nonadjacent _attachment smaller baseline
        obtain ⟨path, pathIsPath, lengthOK⟩ :=
          Graph.AddedEdgeClosure.terminalPath_of_minimal_addedEdge
            object _ u1 u2 different complementAvoids smaller
            baseline minimal
        obtain ⟨exponent, exponentLower, equality⟩ :=
          (Core.DyadicLength.powerOfTwoLength_iff _).mp
            ((accepted _).mp lengthOK)
        exact ⟨path, exponent, pathIsPath, by omega, by omega⟩

/-- **Contraction criticality** (no manuscript label).  Contract one edge whose
common neighbours are not at the threshold.  Avoidance of the accepted
quadrilateral makes the common neighbour unique, so the contraction keeps the
cubic baseline; minimality gives it an accepted cycle, whose two incidences at
the contracted vertex either lift on one side (contradicting avoidance) or are
mixed and splice into a power-of-two severed return. -/
theorem contractionCritical_of_selection
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation}
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (selection : SelectionStatement BranchState Presentation presentation data object)
    (cubicBaseline : CubicBaselineStatement data)
    (lengthOK_iff_powerOfTwo : ∀ length,
      data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    ContractionCriticalStatement data object := by
  have cubic := cubicBaseline.1
  change ∀ contraction : Graph.EdgeContraction object,
    (∀ common : object.Vertex,
      object.graph.Adj contraction.tail common →
      object.graph.Adj contraction.head common →
      object.degree common ≠ data.threshold) →
    ∃ path : contraction.severed.Path contraction.tail contraction.head,
      ∃ exponent : Nat,
        2 ≤ exponent ∧ path.1.length = 2 ^ exponent
  classical
  intro contraction commonNotThreshold
  have accepted : ∀ length,
      data.LengthOK length ↔
        Core.DyadicLength.PowerOfTwoLength length :=
    lengthOK_iff_powerOfTwo
  have baseline : 3 ≤ object.minDegree := by
    rw [← cubic]
    exact baseline
  have avoids := selection.1
  have minimal : ∀ smaller : Graph.FiniteObject.{u},
      smaller.LexicographicallySmaller object →
      3 ≤ smaller.minDegree →
      Graph.HasCycleWithLength data.LengthOK smaller := by
    intro smaller smallerProgress smallerBaseline
    apply selection.2.sizeMinimal smaller smallerProgress
    rw [cubic]
    exact smallerBaseline
  have commonNotCubic : ∀ common : object.Vertex,
      object.graph.Adj contraction.tail common →
      object.graph.Adj contraction.head common →
      object.degree common ≠ 3 := by
    intro common tailCommon headCommon
    intro degreeThree
    apply commonNotThreshold common tailCommon headCommon
    exact degreeThree.trans cubic.symm
  have four : data.LengthOK 4 :=
    (accepted 4).2 Core.DyadicLength.powerOfTwoLength_four
  have commonUnique : ∀ left right : object.Vertex,
      object.graph.Adj contraction.tail left →
      object.graph.Adj contraction.head left →
      object.graph.Adj contraction.tail right →
      object.graph.Adj contraction.head right →
      left = right := by
    intro left right tailLeft headLeft tailRight headRight
    by_contra distinct
    exact Graph.not_quadrilateral avoids four tailLeft headLeft.symm headRight
      tailRight.symm contraction.adjacent.ne distinct
  have contractedBaseline : 3 ≤ contraction.contracted.minDegree := by
    letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
    letI : Nonempty contraction.contracted.Vertex := ⟨contraction.tailVertex⟩
    refine contraction.contracted.le_minDegree_of_forall_le_degree 3 ?_
    intro vertex
    have sourceBaseline : 3 ≤ object.degree vertex.1 :=
      le_trans baseline (object.minDegree_le_degree vertex.1)
    by_cases isTail : vertex = contraction.tailVertex
    · subst isTail
      let leftSet := object.graph.neighborSet contraction.tail \ {contraction.head}
      let rightSet := object.graph.neighborSet contraction.head \ {contraction.tail}
      have imageCard :
          contraction.contracted.degree contraction.tailVertex =
            (leftSet ∪ rightSet).ncard := by
        rw [Graph.FiniteObject.degree_eq_ncard_neighborSet]
        calc
          _ = (Subtype.val ''
              contraction.contracted.graph.neighborSet
                contraction.tailVertex).ncard := by
            exact (Set.ncard_image_of_injective _ Subtype.val_injective).symm
          _ = _ := by rw [contraction.image_neighborSet_tail]
      have leftCard : 2 ≤ leftSet.ncard := by
        have drop := Set.ncard_sdiff_singleton_add_one contraction.adjacent
          (Set.toFinite (object.graph.neighborSet contraction.tail))
        change leftSet.ncard + 1 =
          (object.graph.neighborSet contraction.tail).ncard at drop
        rw [← Graph.FiniteObject.degree_eq_ncard_neighborSet] at drop
        have lower := le_trans baseline
          (object.minDegree_le_degree contraction.tail)
        omega
      have rightCard : 2 ≤ rightSet.ncard := by
        have drop := Set.ncard_sdiff_singleton_add_one contraction.adjacent.symm
          (Set.toFinite (object.graph.neighborSet contraction.head))
        change rightSet.ncard + 1 =
          (object.graph.neighborSet contraction.head).ncard at drop
        rw [← Graph.FiniteObject.degree_eq_ncard_neighborSet] at drop
        have lower := le_trans baseline
          (object.minDegree_le_degree contraction.head)
        omega
      have intersectionCard : (leftSet ∩ rightSet).ncard ≤ 1 := by
        by_cases empty : leftSet ∩ rightSet = ∅
        · simp [empty]
        · obtain ⟨witness, witnessMem⟩ := Set.nonempty_iff_ne_empty.mpr empty
          have subset : leftSet ∩ rightSet ⊆ {witness} := by
            intro other otherMem
            have equality := commonUnique other witness otherMem.1.1
              otherMem.2.1 witnessMem.1.1 witnessMem.2.1
            simpa [equality]
          exact le_trans (Set.ncard_le_ncard subset (Set.toFinite _)) (by simp)
      have unionEquation := Set.ncard_union_add_ncard_inter leftSet rightSet
        (Set.toFinite leftSet) (Set.toFinite rightSet)
      rw [imageCard]
      omega
    · by_cases fromHead : object.graph.Adj contraction.head vertex.1
      · have imageCard : contraction.contracted.degree vertex =
            (insert contraction.tail
              (object.graph.neighborSet vertex.1 \ {contraction.head})).ncard := by
          rw [Graph.FiniteObject.degree_eq_ncard_neighborSet]
          calc
            _ = (Subtype.val ''
                contraction.contracted.graph.neighborSet vertex).ncard := by
              exact (Set.ncard_image_of_injective _ Subtype.val_injective).symm
            _ = _ := by
              rw [contraction.image_neighborSet_of_adj_head isTail fromHead]
        rw [imageCard]
        have headMem : contraction.head ∈ object.graph.neighborSet vertex.1 :=
          fromHead.symm
        have drop := Set.ncard_sdiff_singleton_add_one headMem
          (Set.toFinite (object.graph.neighborSet vertex.1))
        by_cases fromTail : object.graph.Adj contraction.tail vertex.1
        · have nonCubic := commonNotCubic vertex.1 fromTail fromHead
          have sourceDegree : object.degree vertex.1 ≠ 3 := nonCubic
          have lower : 4 ≤ object.degree vertex.1 := by omega
          have insertBound := Set.ncard_le_ncard_insert contraction.tail
            (object.graph.neighborSet vertex.1 \ {contraction.head})
          rw [← Graph.FiniteObject.degree_eq_ncard_neighborSet] at drop
          omega
        · have tailNotMem : contraction.tail ∉
              object.graph.neighborSet vertex.1 \ {contraction.head} := by
            rintro ⟨tailAdj, _⟩
            exact fromTail tailAdj.symm
          rw [Set.ncard_insert_of_notMem tailNotMem (Set.toFinite _)]
          rw [← Graph.FiniteObject.degree_eq_ncard_neighborSet] at drop
          omega
      · have imageCard : contraction.contracted.degree vertex =
            (object.graph.neighborSet vertex.1).ncard := by
          rw [Graph.FiniteObject.degree_eq_ncard_neighborSet]
          calc
            _ = (Subtype.val ''
                contraction.contracted.graph.neighborSet vertex).ncard := by
              exact (Set.ncard_image_of_injective _ Subtype.val_injective).symm
            _ = _ := by
              rw [contraction.image_neighborSet_of_ne_tail isTail fromHead]
        rw [imageCard, ← Graph.FiniteObject.degree_eq_ncard_neighborSet]
        exact sourceBaseline
  obtain ⟨certificate⟩ := minimal contraction.contracted
    contraction.lexicographicallySmaller contractedBaseline
  by_cases tailMem : contraction.tailVertex ∈ certificate.walk.support
  · let rotated := certificate.walk.rotate contraction.tailVertex tailMem
    have rotatedCycle : rotated.IsCycle := certificate.isCycle.rotate tailMem
    have rotatedLength : rotated.length = certificate.walk.length :=
      certificate.walk.length_rotate contraction.tailVertex tailMem
    let rotatedCertificate :
    Graph.CycleCertificate contraction.contracted data.LengthOK :=
      { vertex := contraction.tailVertex
        walk := rotated
        isCycle := rotatedCycle
        length_ok := rotatedLength ▸ certificate.length_ok }
    have notNil : ¬ rotated.Nil := rotatedCycle.not_nil
    have firstAdj : contraction.contracted.graph.Adj
        contraction.tailVertex rotated.snd := rotated.adj_snd notNil
    have rebuilt : (SimpleGraph.Walk.cons firstAdj rotated.tail).IsCycle := by
      rw [rotated.cons_tail_eq notNil]
      exact rotatedCycle
    have forwardData :=
      (SimpleGraph.Walk.cons_isCycle_iff rotated.tail firstAdj).mp rebuilt
    let back := rotated.tail.reverse
    have backPath : back.IsPath := forwardData.1.reverse
    have backNotNil : ¬ back.Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      have three := rotatedCycle.three_le_length
      have drop := rotated.length_tail_add_one notNil
      have reversed : back.length = rotated.tail.length :=
        SimpleGraph.Walk.length_reverse rotated.tail
      omega
    have secondAdj : contraction.contracted.graph.Adj
        contraction.tailVertex back.snd := back.adj_snd backNotNil
    have backRebuilt : (SimpleGraph.Walk.cons secondAdj back.tail).IsPath := by
      rw [back.cons_tail_eq backNotNil]
      exact backPath
    have backData :=
      (SimpleGraph.Walk.cons_isPath_iff secondAdj back.tail).mp backRebuilt
    have edgeCases : ∀ edge ∈ rotated.edges,
        edge = s(contraction.tailVertex, rotated.snd) ∨
          edge = s(contraction.tailVertex, back.snd) ∨
            edge ∈ back.tail.edges := by
      intro edge member
      rw [← rotated.cons_tail_eq notNil, SimpleGraph.Walk.edges_cons,
        List.mem_cons] at member
      rcases member with first | later
      · exact Or.inl first
      · have inBack : edge ∈ back.edges := by
          change edge ∈ rotated.tail.reverse.edges
          rw [SimpleGraph.Walk.edges_reverse]
          exact List.mem_reverse.mpr later
        rw [← back.cons_tail_eq backNotNil, SimpleGraph.Walk.edges_cons,
          List.mem_cons] at inBack
        rcases inBack with second | inner
        · exact Or.inr (Or.inl second)
        · exact Or.inr (Or.inr inner)
    have inner : ∀ label : contraction.contracted.Vertex → object.Vertex,
        (∀ vertex : contraction.contracted.Vertex,
          vertex ≠ contraction.tailVertex → label vertex = vertex.1) →
        ∀ edge ∈ back.tail.edges,
          edge ∈ (contraction.pullback label).graph.edgeSet := by
      intro label agrees edge member
      revert member
      induction edge using Sym2.ind with
      | _ left right =>
        intro member
        have leftNe : left ≠ contraction.tailVertex := by
          rintro rfl
          exact backData.2 (back.tail.fst_mem_support_of_mem_edges member)
        have rightNe : right ≠ contraction.tailVertex := by
          rintro rfl
          exact backData.2 (back.tail.snd_mem_support_of_mem_edges member)
        have adjacent : object.graph.Adj left.1 right.1 :=
          (contraction.contracted_adj_of_ne_tail leftNe rightNe).mp
            (back.tail.edges_subset_edgeSet member)
        show object.graph.Adj (label left) (label right)
        rw [agrees left leftNe, agrees right rightNe]
        exact adjacent
    obtain ⟨forwardNotTail, forwardKind⟩ :=
      (contraction.contracted_adj_tail rotated.snd).mp firstAdj
    obtain ⟨backNotTail, backKind⟩ :=
      (contraction.contracted_adj_tail back.snd).mp secondAdj
    have exactDyadic (path : contraction.severed.Path
        contraction.tail contraction.head)
        (pathLength : path.1.length = back.tail.length + 2) :
        ∃ exponent : Nat, 2 ≤ exponent ∧ path.1.length = 2 ^ exponent := by
      have cycleLength : certificate.walk.length = back.tail.length + 2 := by
        have firstDrop := rotated.length_tail_add_one notNil
        have reversed : back.length = rotated.tail.length :=
          SimpleGraph.Walk.length_reverse rotated.tail
        have secondDrop := back.length_tail_add_one backNotNil
        omega
      obtain ⟨exponent, lower, power⟩ :=
        (Core.DyadicLength.powerOfTwoLength_iff certificate.walk.length).1
          ((accepted certificate.walk.length).1 certificate.length_ok)
      exact ⟨exponent, lower, by omega⟩
    rcases forwardKind with forwardTail | forwardHead
    · rcases backKind with backTail | backHead
      · exfalso
        apply avoids
        exact ⟨contraction.certificateOfPullback Subtype.val
          Subtype.val_injective rotatedCertificate (by
            intro edge member
            rcases edgeCases edge member with first | second | later
            · exact first ▸ forwardTail
            · exact second ▸ backTail
            · exact inner Subtype.val (fun _ _ => rfl) edge later)⟩
      · obtain ⟨path, pathLength⟩ :=
          contraction.exactReturn_of_mixed_incidences back.tail backData.1
            backData.2 backHead forwardTail
        exact ⟨path, exactDyadic path pathLength⟩
    · rcases backKind with backTail | backHead
      · obtain ⟨path, pathLength⟩ :=
          contraction.exactReturn_of_mixed_incidences back.tail.reverse
            backData.1.reverse (by
              rw [SimpleGraph.Walk.support_reverse]
              exact fun member => backData.2 (List.mem_reverse.mp member))
            forwardHead backTail
        refine ⟨path, ?_⟩
        apply exactDyadic path
        rw [pathLength, SimpleGraph.Walk.length_reverse]
      · exfalso
        apply avoids
        exact ⟨contraction.certificateOfPullback contraction.merge
          contraction.merge_injective rotatedCertificate (by
            intro edge member
            rcases edgeCases edge member with first | second | later
            · rw [first]
              show object.graph.Adj
                (contraction.merge contraction.tailVertex)
                (contraction.merge rotated.snd)
              rw [contraction.merge_tailVertex,
                contraction.merge_of_ne_tail forwardNotTail]
              exact forwardHead
            · rw [second]
              show object.graph.Adj
                (contraction.merge contraction.tailVertex)
                (contraction.merge back.snd)
              rw [contraction.merge_tailVertex,
                contraction.merge_of_ne_tail backNotTail]
              exact backHead
            · exact inner contraction.merge
                (fun _ notTail => contraction.merge_of_ne_tail notTail)
                edge later)⟩
  · exfalso
    apply avoids
    exact ⟨contraction.certificateOfPullback Subtype.val
      Subtype.val_injective certificate (by
        intro edge member
        revert member
        induction edge using Sym2.ind with
        | _ left right =>
          intro member
          have leftNe : left ≠ contraction.tailVertex := by
            rintro rfl
            exact tailMem (certificate.walk.fst_mem_support_of_mem_edges member)
          have rightNe : right ≠ contraction.tailVertex := by
            rintro rfl
            exact tailMem (certificate.walk.snd_mem_support_of_mem_edges member)
          exact (contraction.contracted_adj_of_ne_tail leftNe rightNe).mp
            (certificate.walk.edges_subset_edgeSet member))⟩

end Hypostructure.Graph.Contracts.Spine
