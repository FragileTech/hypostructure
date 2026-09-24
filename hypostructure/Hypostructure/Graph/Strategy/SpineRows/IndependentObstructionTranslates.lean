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

/-! ## Nodes `[51]`--`[52]`: independent obstruction translates

`lem:translates-independent` is not an entropy inequality.  On the literal
full-rank remainder, a dominant rooted radius-`r` type containing an internal
root wedge supplies a translated raw wedge at every dominant centre.  Choose a
maximum `2r`-separated set of those centres.  Maximality covers the dominant set
by radius-`2r` balls; the radius-`r` balls are pairwise disjoint; and
`SubcubicReach.card_reach_le` gives the manuscript's exact bound
`b' = 1 + 3(2^(2r)-1)`.  Distinct centres give distinct raw wedge labels, and
the incoming full-rank fact identifies their supply with `r_Ω(R)`.

The committed statement is the division-free finite form
`|R| ≤ b'·r_Ω(R) + T(n)`, where the already registered near-cubic
threshold `T(n)` is the finite representative of the manuscript's `o(|R|)`
set.  No unbounded existential error is admitted. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def independentObstructionTranslatesRow :
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
    `Hypostructure.Graph.Strategy.Spine.independentObstructionTranslates
    { Requires := [K .curvatureFullRank, K .dominantRootedWedgeType]
      Produces := [K .independentObstructionTranslates]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _fullRank := (inputs.get (K .curvatureFullRank)).down
      let dominantInput := (inputs.get (K .dominantRootedWedgeType)).down
      .cons (key := K .independentObstructionTranslates)
        (show Value BranchState Presentation presentation data
            .independentObstructionTranslates inputs.current from ⟨by
          classical
          obtain ⟨packing, valid, maximal, rankEq, dominant, root,
            dominantSubset, rootMem, dominantCount, sameType, rootWedge⟩ :=
            dominantInput
          let radius := 2
          refine ⟨packing, valid, maximal, radius, by simp [radius], ?_⟩
          let support := inputs.current.object.remainderSupport packing
          let subcubic := remainderSubcubicSupport data inputs.current.object packing
          have subcubicSubsetSupport : subcubic ⊆ support := by
            intro vertex member
            exact (Finset.mem_filter.mp member).1
          have dominantSubsetSupport : dominant ⊆ support :=
            dominantSubset.trans subcubicSubsetSupport
          change support.card ≤ dominant.card +
            2 * data.surplusThreshold inputs.current.object.vertexCount at dominantCount
          change support.card ≤
            (1 + data.threshold *
                ((data.threshold - 1) ^ (2 * radius) - 1)) *
              remainderCurvatureTargetRank data inputs.current.object packing +
                2 * data.surplusThreshold inputs.current.object.vertexCount
          have rootedWedges : ∀ vertex ∈ dominant,
              ∃ wedge : inputs.current.object.InternalWedge support,
                wedge.1 = vertex ∧
                  wedge ∈ inputs.current.object.internalWedgeFamily support := by
            intro vertex member
            have localWedge :=
              inputs.current.object.rootedInternalWedgeClause_of_code_eq
                subcubic radius
                ⟨root, dominantSubset rootMem⟩
                ⟨vertex, dominantSubset member⟩
                (sameType vertex member) rootWedge
            obtain ⟨wedge, centre, familyMember⟩ := localWedge
            let enlarged := inputs.current.object.internalWedgeOfSubset
              subcubicSubsetSupport wedge
            refine ⟨enlarged, ?_, ?_⟩
            · simpa [enlarged, Graph.FiniteObject.internalWedgeOfSubset] using centre
            · exact inputs.current.object.internalWedgeOfSubset_mem_family
                subcubicSubsetSupport wedge familyMember
          letI : FinEnum inputs.current.object.Vertex :=
            inputs.current.object.vertices
          letI : Fintype inputs.current.object.Vertex := inferInstance
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          letI : DecidableRel inputs.current.object.graph.Adj :=
            inputs.current.object.decideAdj
          let ball := fun centre : inputs.current.object.Vertex =>
            Graph.SubcubicReach.reach inputs.current.object.graph subcubic centre
                (2 * radius) centre ∩ subcubic
          have reverseReach : ∀ {left right : inputs.current.object.Vertex},
              left ∈ subcubic → right ∈ subcubic →
                right ∈ ball left → left ∈ ball right := by
            intro left right leftMem rightMem member
            obtain ⟨memberReach, _memberSupport⟩ := Finset.mem_inter.mp member
            obtain ⟨path, pathIsPath, pathLength, pathInside, _pathAvoids⟩ :=
              (Graph.SubcubicReach.mem_reach inputs.current.object.graph).1 memberReach
            apply Finset.mem_inter.mpr
            refine ⟨(Graph.SubcubicReach.mem_reach inputs.current.object.graph).2
              ⟨path.reverse, pathIsPath.reverse, ?_, ?_, ?_⟩, leftMem⟩
            · simpa [ball, SimpleGraph.Walk.length_reverse] using pathLength
            · intro vertex vertexMem
              have reverseSupport : vertex ∈ path.reverse.support :=
                List.mem_of_mem_dropLast vertexMem
              rw [SimpleGraph.Walk.support_reverse] at reverseSupport
              have originalSupport : vertex ∈ path.support := by
                simpa using reverseSupport
              by_cases atEnd : vertex = right
              · simpa [atEnd] using rightMem
              · apply pathInside vertex
                apply List.mem_dropLast_of_mem_of_ne_getLast originalSupport
                simpa [SimpleGraph.Walk.getLast_support] using atEnd
            · intro notNil same
              have indexZero :=
                (pathIsPath.reverse.getVert_eq_start_iff_of_not_nil
                  (i := 1) notNil).1 same
              exact absurd indexZero (by decide)
          have ballSymm : ∀ {left right : inputs.current.object.Vertex},
              left ∈ subcubic → right ∈ subcubic →
                (right ∈ ball left ↔ left ∈ ball right) := by
            intro left right leftMem rightMem
            exact ⟨reverseReach leftMem rightMem, reverseReach rightMem leftMem⟩
          let candidates : Finset (Finset inputs.current.object.Vertex) :=
            dominant.powerset.filter fun selected =>
              (selected : Set inputs.current.object.Vertex).Pairwise
                fun left right => right ∉ ball left
          have candidatesNonempty : candidates.Nonempty := by
            refine ⟨∅, ?_⟩
            simp [candidates]
          obtain ⟨selected, selectedMem, maximalSelected⟩ :=
            Finset.exists_max_image candidates Finset.card candidatesNonempty
          have selectedSubset : selected ⊆ dominant :=
            (Finset.mem_filter.mp selectedMem).1 |> Finset.mem_powerset.mp
          have selectedSeparated :
              (selected : Set inputs.current.object.Vertex).Pairwise
                fun left right => right ∉ ball left :=
            (Finset.mem_filter.mp selectedMem).2
          have covers : dominant ⊆ selected.biUnion ball := by
            intro vertex vertexMem
            by_contra uncovered
            have vertexNotSelected : vertex ∉ selected := by
              intro member
              apply uncovered
              exact Finset.mem_biUnion.mpr ⟨vertex, member,
                Finset.mem_inter.mpr
                  ⟨Graph.SubcubicReach.self_mem_reach
                      inputs.current.object.graph subcubic vertex (2 * radius) vertex,
                    dominantSubset vertexMem⟩⟩
            have separatedInsert :
                ((insert vertex selected : Finset inputs.current.object.Vertex) :
                    Set inputs.current.object.Vertex).Pairwise
                  (fun left right => right ∉ ball left) := by
              rw [Finset.coe_insert, Set.pairwise_insert_of_notMem vertexNotSelected]
              refine ⟨selectedSeparated, ?_⟩
              intro other otherMem
              have otherSupport : other ∈ subcubic :=
                dominantSubset (selectedSubset otherMem)
              have vertexSupport : vertex ∈ subcubic := dominantSubset vertexMem
              have notCovered : vertex ∉ ball other := by
                intro covered
                apply uncovered
                exact Finset.mem_biUnion.mpr ⟨other, otherMem, covered⟩
              exact ⟨(ballSymm vertexSupport otherSupport).not.mpr notCovered,
                notCovered⟩
            have insertMem : insert vertex selected ∈ candidates := by
              rw [Finset.mem_filter, Finset.mem_powerset]
              exact ⟨Finset.insert_subset vertexMem selectedSubset, separatedInsert⟩
            have maximalCard := maximalSelected (insert vertex selected) insertMem
            rw [Finset.card_insert_of_notMem vertexNotSelected] at maximalCard
            omega
          have ballCard : ∀ centre ∈ selected,
              (ball centre).card ≤ 1 + data.threshold *
                ((data.threshold - 1) ^ (2 * radius) - 1) := by
            intro centre _centreMem
            have paperBound :=
              (Graph.SubcubicReach.card_reach_le inputs.current.object.graph
                subcubic (by
                  intro vertex member
                  change inputs.current.object.degree vertex ≤ 3
                  simpa [data.threshold_eq_three] using
                    (Finset.mem_filter.mp member).2)
                centre (2 * radius))
            simpa [data.threshold_eq_three] using
              (Finset.card_le_card Finset.inter_subset_left).trans paperBound
          let smallBall := fun centre : inputs.current.object.Vertex =>
            Graph.SubcubicReach.reach inputs.current.object.graph subcubic centre
                radius centre ∩ subcubic
          have _separatedBalls : ∀ left ∈ selected, ∀ right ∈ selected,
              left ≠ right → Disjoint (smallBall left) (smallBall right) := by
            intro left leftMem right rightMem different
            apply Finset.disjoint_left.mpr
            intro vertex vertexLeft vertexRight
            obtain ⟨leftReach, vertexSupport⟩ := Finset.mem_inter.mp vertexLeft
            obtain ⟨rightReach, _vertexSupport⟩ := Finset.mem_inter.mp vertexRight
            obtain ⟨leftPath, leftIsPath, leftLength, leftInside, _leftAvoids⟩ :=
              (Graph.SubcubicReach.mem_reach inputs.current.object.graph).1 leftReach
            obtain ⟨rightPath, rightIsPath, rightLength, rightInside,
              _rightAvoids⟩ :=
              (Graph.SubcubicReach.mem_reach inputs.current.object.graph).1 rightReach
            let joined := leftPath.append rightPath.reverse
            let reduced := joined.toPath
            have joinedInside : ∀ member ∈ joined.support, member ∈ subcubic := by
              intro member memberMem
              rw [SimpleGraph.Walk.mem_support_append_iff] at memberMem
              rcases memberMem with memberMem | memberMem
              · by_cases atEnd : member = vertex
                · simpa [atEnd] using vertexSupport
                · apply leftInside member
                  apply List.mem_dropLast_of_mem_of_ne_getLast memberMem
                  simpa [SimpleGraph.Walk.getLast_support] using atEnd
              · rw [SimpleGraph.Walk.support_reverse] at memberMem
                have originalMem : member ∈ rightPath.support := by
                  simpa using memberMem
                by_cases atEnd : member = vertex
                · simpa [atEnd] using vertexSupport
                · apply rightInside member
                  apply List.mem_dropLast_of_mem_of_ne_getLast originalMem
                  simpa [SimpleGraph.Walk.getLast_support] using atEnd
            have reducedLength :
                (reduced : inputs.current.object.graph.Walk left right).length ≤
                  2 * radius := by
              calc
                (reduced : inputs.current.object.graph.Walk left right).length ≤
                    joined.length :=
                  SimpleGraph.Walk.length_bypass_le_length joined
                _ = leftPath.length + rightPath.length := by
                  simp [joined, SimpleGraph.Walk.length_append,
                    SimpleGraph.Walk.length_reverse]
                _ ≤ radius + radius := Nat.add_le_add leftLength rightLength
                _ = 2 * radius := by omega
            have reducedInside : ∀ member ∈
                (reduced : inputs.current.object.graph.Walk left right).support.dropLast,
                member ∈ subcubic := by
              intro member memberMem
              apply joinedInside member
              exact SimpleGraph.Walk.support_toPath_subset_support joined
                (List.mem_of_mem_dropLast memberMem)
            have reducedAvoids : ∀ notNil :
                ¬ (reduced : inputs.current.object.graph.Walk left right).Nil,
                (reduced : inputs.current.object.graph.Walk left right).getVert 1 ≠
                  left := by
              intro notNil same
              have indexZero :=
                (reduced.property.getVert_eq_start_iff_of_not_nil
                  (i := 1) notNil).1 same
              exact absurd indexZero (by decide)
            have rightCovered : right ∈ ball left := Finset.mem_inter.mpr ⟨
              (Graph.SubcubicReach.mem_reach inputs.current.object.graph).2
                ⟨reduced, reduced.property, reducedLength, reducedInside,
                  reducedAvoids⟩,
              dominantSubset (selectedSubset rightMem)⟩
            exact (selectedSeparated leftMem rightMem different) rightCovered
          have dominantLe : dominant.card ≤
              (1 + data.threshold *
                  ((data.threshold - 1) ^ (2 * radius) - 1)) * selected.card := by
            calc
              dominant.card ≤ (selected.biUnion ball).card :=
                Finset.card_le_card covers
              _ ≤ ∑ centre ∈ selected, (ball centre).card :=
                Finset.card_biUnion_le
              _ ≤ ∑ _centre ∈ selected,
                  (1 + data.threshold *
                    ((data.threshold - 1) ^ (2 * radius) - 1)) :=
                Finset.sum_le_sum ballCard
              _ = (1 + data.threshold *
                    ((data.threshold - 1) ^ (2 * radius) - 1)) * selected.card := by
                rw [Finset.sum_const, nsmul_eq_mul]
                exact Nat.mul_comm _ _
          let wedgeAt : {vertex // vertex ∈ selected} →
              inputs.current.object.InternalWedge support := fun vertex =>
            Classical.choose (rootedWedges vertex.1 (selectedSubset vertex.2))
          have wedgeAtSpec : ∀ vertex : {vertex // vertex ∈ selected},
              (wedgeAt vertex).1 = vertex.1 ∧
                wedgeAt vertex ∈ inputs.current.object.internalWedgeFamily support := by
            intro vertex
            exact Classical.choose_spec
              (rootedWedges vertex.1 (selectedSubset vertex.2))
          let translates := selected.attach.image wedgeAt
          have wedgeInjective : Function.Injective wedgeAt := by
            intro left right equal
            apply Subtype.ext
            have leftCentre := (wedgeAtSpec left).1
            have rightCentre := (wedgeAtSpec right).1
            exact leftCentre.symm.trans (congrArg Sigma.fst equal) |>.trans rightCentre
          have translatesCard : translates.card = selected.card := by
            rw [show translates = selected.attach.image wedgeAt from rfl,
              Finset.card_image_of_injective _ wedgeInjective, Finset.card_attach]
          have translatesSubset :
              translates ⊆ inputs.current.object.internalWedgeFamily support := by
            intro wedge wedgeMem
            obtain ⟨vertex, _vertexMem, rfl⟩ := Finset.mem_image.mp wedgeMem
            exact (wedgeAtSpec vertex).2
          have rankEq' : remainderCurvatureTargetRank data inputs.current.object packing =
              inputs.current.object.internalWedgeCount support := by
            simpa only [support, remainderWedgeSupply] using rankEq
          have selectedLeRank : selected.card ≤
              remainderCurvatureTargetRank data inputs.current.object packing := by
            rw [← translatesCard, rankEq',
              ← inputs.current.object.internalWedgeFamily_card support]
            exact Finset.card_le_card translatesSubset
          have dominantLeRank : dominant.card ≤
              (1 + data.threshold *
                  ((data.threshold - 1) ^ (2 * radius) - 1)) *
                remainderCurvatureTargetRank data inputs.current.object packing :=
            dominantLe.trans (Nat.mul_le_mul_left _ selectedLeRank)
          omega⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
