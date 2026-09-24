import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Contraction criticality (no manuscript label; not a manuscript statement)

Contract one edge whose common neighbours are not cubic.  Avoidance of the
accepted quadrilateral makes that common neighbour unique; hence contraction
preserves the cubic baseline.  Selection minimality supplies an accepted
cycle of the contraction.  Its two incidences at the contracted vertex either
lift on one side, contradicting avoidance, or are mixed and splice into a
power-of-two severed return. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def contractionCriticalRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.contractionCritical
    { Requires := [K .selection, K .cubicBaseline]
      Produces := [K .contractionCritical]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selection := (inputs.get (K .selection)).down
      let cubic := (inputs.get (K .cubicBaseline)).down.1
      .cons (key := K .contractionCritical) ⟨by
        change ∀ contraction : Graph.EdgeContraction inputs.current.object,
          (∀ common : inputs.current.object.Vertex,
            inputs.current.object.graph.Adj contraction.tail common →
            inputs.current.object.graph.Adj contraction.head common →
            inputs.current.object.degree common ≠ data.threshold) →
          ∃ path : contraction.severed.Path contraction.tail contraction.head,
            ∃ exponent : Nat,
              2 ≤ exponent ∧ path.1.length = 2 ^ exponent
        classical
        intro contraction commonNotThreshold
        have accepted : ∀ length,
            data.LengthOK length ↔
              Core.DyadicLength.PowerOfTwoLength length :=
          data.lengthOK_iff_powerOfTwo
        have baseline : 3 ≤ inputs.current.object.minDegree := by
          rw [← cubic]
          exact inputs.current.baseline
        have avoids := selection.1
        have minimal : ∀ smaller : Graph.FiniteObject.{u},
            smaller.LexicographicallySmaller inputs.current.object →
            3 ≤ smaller.minDegree →
            Graph.HasCycleWithLength data.LengthOK smaller := by
          intro smaller smallerProgress smallerBaseline
          apply selection.2.sizeMinimal smaller smallerProgress
          rw [cubic]
          exact smallerBaseline
        have commonNotCubic : ∀ common : inputs.current.object.Vertex,
            inputs.current.object.graph.Adj contraction.tail common →
            inputs.current.object.graph.Adj contraction.head common →
            inputs.current.object.degree common ≠ 3 := by
          intro common tailCommon headCommon
          intro degreeThree
          apply commonNotThreshold common tailCommon headCommon
          exact degreeThree.trans cubic.symm
        have four : data.LengthOK 4 :=
          (accepted 4).2 Core.DyadicLength.powerOfTwoLength_four
        have commonUnique : ∀ left right : inputs.current.object.Vertex,
            inputs.current.object.graph.Adj contraction.tail left →
            inputs.current.object.graph.Adj contraction.head left →
            inputs.current.object.graph.Adj contraction.tail right →
            inputs.current.object.graph.Adj contraction.head right →
            left = right := by
          intro left right tailLeft headLeft tailRight headRight
          by_contra distinct
          exact Graph.not_quadrilateral avoids four tailLeft headLeft.symm headRight
            tailRight.symm contraction.adjacent.ne distinct
        have contractedBaseline : 3 ≤ contraction.contracted.minDegree := by
          letI : Fintype inputs.current.object.Vertex := @FinEnum.instFintype _ inputs.current.object.vertices
          letI : Nonempty contraction.contracted.Vertex := ⟨contraction.tailVertex⟩
          refine contraction.contracted.le_minDegree_of_forall_le_degree 3 ?_
          intro vertex
          have sourceBaseline : 3 ≤ inputs.current.object.degree vertex.1 :=
            le_trans baseline (inputs.current.object.minDegree_le_degree vertex.1)
          by_cases isTail : vertex = contraction.tailVertex
          · subst isTail
            let leftSet := inputs.current.object.graph.neighborSet contraction.tail \ {contraction.head}
            let rightSet := inputs.current.object.graph.neighborSet contraction.head \ {contraction.tail}
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
                (Set.toFinite (inputs.current.object.graph.neighborSet contraction.tail))
              change leftSet.ncard + 1 =
                (inputs.current.object.graph.neighborSet contraction.tail).ncard at drop
              rw [← Graph.FiniteObject.degree_eq_ncard_neighborSet] at drop
              have lower := le_trans baseline
                (inputs.current.object.minDegree_le_degree contraction.tail)
              omega
            have rightCard : 2 ≤ rightSet.ncard := by
              have drop := Set.ncard_sdiff_singleton_add_one contraction.adjacent.symm
                (Set.toFinite (inputs.current.object.graph.neighborSet contraction.head))
              change rightSet.ncard + 1 =
                (inputs.current.object.graph.neighborSet contraction.head).ncard at drop
              rw [← Graph.FiniteObject.degree_eq_ncard_neighborSet] at drop
              have lower := le_trans baseline
                (inputs.current.object.minDegree_le_degree contraction.head)
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
          · by_cases fromHead : inputs.current.object.graph.Adj contraction.head vertex.1
            · have imageCard : contraction.contracted.degree vertex =
                  (insert contraction.tail
                    (inputs.current.object.graph.neighborSet vertex.1 \ {contraction.head})).ncard := by
                rw [Graph.FiniteObject.degree_eq_ncard_neighborSet]
                calc
                  _ = (Subtype.val ''
                      contraction.contracted.graph.neighborSet vertex).ncard := by
                    exact (Set.ncard_image_of_injective _ Subtype.val_injective).symm
                  _ = _ := by
                    rw [contraction.image_neighborSet_of_adj_head isTail fromHead]
              rw [imageCard]
              have headMem : contraction.head ∈ inputs.current.object.graph.neighborSet vertex.1 :=
                fromHead.symm
              have drop := Set.ncard_sdiff_singleton_add_one headMem
                (Set.toFinite (inputs.current.object.graph.neighborSet vertex.1))
              by_cases fromTail : inputs.current.object.graph.Adj contraction.tail vertex.1
              · have nonCubic := commonNotCubic vertex.1 fromTail fromHead
                have sourceDegree : inputs.current.object.degree vertex.1 ≠ 3 := nonCubic
                have lower : 4 ≤ inputs.current.object.degree vertex.1 := by omega
                have insertBound := Set.ncard_le_ncard_insert contraction.tail
                  (inputs.current.object.graph.neighborSet vertex.1 \ {contraction.head})
                rw [← Graph.FiniteObject.degree_eq_ncard_neighborSet] at drop
                omega
              · have tailNotMem : contraction.tail ∉
                    inputs.current.object.graph.neighborSet vertex.1 \ {contraction.head} := by
                  rintro ⟨tailAdj, _⟩
                  exact fromTail tailAdj.symm
                rw [Set.ncard_insert_of_notMem tailNotMem (Set.toFinite _)]
                rw [← Graph.FiniteObject.degree_eq_ncard_neighborSet] at drop
                omega
            · have imageCard : contraction.contracted.degree vertex =
                  (inputs.current.object.graph.neighborSet vertex.1).ncard := by
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
          have inner : ∀ label : contraction.contracted.Vertex → inputs.current.object.Vertex,
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
              have adjacent : inputs.current.object.graph.Adj left.1 right.1 :=
                (contraction.contracted_adj_of_ne_tail leftNe rightNe).mp
                  (back.tail.edges_subset_edgeSet member)
              show inputs.current.object.graph.Adj (label left) (label right)
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
                    show inputs.current.object.graph.Adj
                      (contraction.merge contraction.tailVertex)
                      (contraction.merge rotated.snd)
                    rw [contraction.merge_tailVertex,
                      contraction.merge_of_ne_tail forwardNotTail]
                    exact forwardHead
                  · rw [second]
                    show inputs.current.object.graph.Adj
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
        ⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
