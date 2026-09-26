import Hypostructure.Graph.Statements.SpineDominantType

/-!
# Contracts: the dominant rooted type and its translates, `[51]`--`[52]`

Proof-agnostic contract lemmas for `lem:dominant-type` and
`lem:translates-independent`.  Each lemma is stated over a
`Graph.FiniteObject` with the registered `Parameters` as a parameter and every
paper hypothesis explicit; its conclusion is exactly the statement of the fact
it proves.  This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[50]`, `prop:two-budget` (b).**  On the full-rank remainder of the
fixed maximum packing, a structurally repetitive radius-two type coordinate. -/
theorem localTypeCoordinateRepetitive_of_fullRank (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (fullRank : CurvatureFullRankStatement data object)
    (repetitive : RemainderTypeCoordinateRepetitive data object
      (canonicalWindowPacking data object)) :
    LocalTypeCoordinateRepetitiveStatement data object := by
  obtain ⟨packing, canonical, valid, maximal, rankEq⟩ := fullRank
  subst canonical
  exact ⟨_, rfl, valid, maximal, rankEq, repetitive⟩

/-- **Node `[50]`, `prop:two-budget` (c).**  On the full-rank remainder of the
fixed maximum packing, the radius-two type coordinate is not structurally
repetitive. -/
theorem localTypeCoordinateNonrepetitive_of_fullRank (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (fullRank : CurvatureFullRankStatement data object)
    (nonrepetitive : ¬ RemainderTypeCoordinateRepetitive data object
      (canonicalWindowPacking data object)) :
    LocalTypeCoordinateNonrepetitiveStatement data object := by
  obtain ⟨packing, canonical, valid, maximal, rankEq⟩ := fullRank
  subst canonical
  exact ⟨_, rfl, valid, maximal, rankEq, nonrepetitive⟩

set_option maxHeartbeats 1000000 in
/-- **Node `[51]`, `lem:dominant-type`.**  The repetitive maximum-packing
coordinate is a finite relabelling-orbit statement: its multinomial threshold
supplies a fibre covering all but `T(n)` vertices of the subcubic remainder,
and at most another `T(n)` remainder vertices exceed the baseline degree, by
the near-cubic surplus bound. -/
theorem dominantRootedType_of_repetitive (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (repetitiveInput : LocalTypeCoordinateRepetitiveStatement data object)
    (nearCubic : SurplusAtOrBelowStatement data object) :
    DominantRootedTypeSchema data object := by
  classical
  obtain ⟨packing', canonical, _valid, _maximal, rankEq, repetitive⟩ := repetitiveInput
  subst canonical
  set packing := canonicalWindowPacking data object with packingDef
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := inferInstance
  letI : DecidableEq object.Vertex := Classical.decEq object.Vertex
  let support := object.remainderSupport packing
  let subcubic := remainderSubcubicSupport data object packing
  have repetitive' :=
    (remainderTypeCoordinateRepetitive_iff data object packing).mp repetitive
  obtain ⟨root, fibreCount⟩ :=
    Graph.RootedLocalType.exists_dominant_of_structurallyRepetitive
      (object.rootedLocalTypeCode
        (remainderSubcubicSupport data object packing) 2)
      (data.surplusThreshold object.vertexCount) repetitive'
  let code := object.rootedLocalTypeCode subcubic 2
  let fibre := Graph.RootedLocalType.typeFibre code root
  let dominant : Finset object.Vertex := fibre.image Subtype.val
  have dominantSubset : dominant ⊆ subcubic := by
    intro vertex member
    obtain ⟨localVertex, _localMember, rfl⟩ := Finset.mem_image.mp member
    exact localVertex.2
  have rootFibre : root ∈ fibre := by
    simp [fibre, Graph.RootedLocalType.typeFibre]
  have rootMem : root.1 ∈ dominant := by
    exact Finset.mem_image.mpr ⟨root, rootFibre, rfl⟩
  have dominantCard : dominant.card = fibre.card := by
    rw [show dominant = fibre.image Subtype.val from rfl,
      Finset.card_image_of_injective _ Subtype.val_injective]
  have subcubicLe : subcubic.card ≤ dominant.card +
      data.surplusThreshold object.vertexCount := by
    rw [Fintype.card_coe, ← dominantCard] at fibreCount
    exact fibreCount
  let high := support.filter fun vertex =>
    ¬ object.degree vertex ≤ data.threshold
  have baselineDegree : ∀ vertex : object.Vertex,
      data.threshold ≤ object.degree vertex := fun vertex =>
    le_trans baseline (object.minDegree_le_degree vertex)
  have highCard : high.card ≤ object.degreeSurplus data.threshold := by
    calc
      high.card = ∑ _vertex ∈ high, 1 := by simp
      _ ≤ ∑ vertex ∈ high,
            (object.degree vertex - data.threshold) := by
        exact Finset.sum_le_sum fun vertex member => by
          have above := (Finset.mem_filter.mp member).2
          omega
      _ ≤ ∑ vertex ∈ (Finset.univ : Finset object.Vertex),
            (object.degree vertex - data.threshold) := by
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ high)
      _ = object.degreeSurplus data.threshold := by
        simpa [Graph.FiniteObject.ambientSurplus] using
          object.ambientSurplus_univ_eq_degreeSurplus
            data.threshold baselineDegree
  have highLe : high.card ≤
      data.surplusThreshold object.vertexCount := highCard.trans nearCubic
  have supportSplit : subcubic.card + high.card = support.card := by
    simpa [subcubic, remainderSubcubicSupport, high] using
      support.card_filter_add_card_filter_not
        (fun vertex => object.degree vertex ≤ data.threshold)
  have supportCount : support.card ≤ dominant.card +
      2 * data.surplusThreshold object.vertexCount := by
    omega
  refine ⟨rankEq, ?_⟩
  obtain ⟨dominantRoot, canonicalEq, _⟩ :=
    canonicalDominantRootedType?_spec (data := data) (object := object)
      ⟨(dominant, root.1), dominantSubset, rootMem, supportCount, by
        intro vertex vertexMem
        obtain ⟨localVertex, localMember, localValue⟩ :=
          Finset.mem_image.mp vertexMem
        have equalToRoot : code localVertex = code root :=
          (Finset.mem_filter.mp localMember).2
        subst vertex
        exact equalToRoot.symm⟩
  exact ⟨dominantRoot, canonicalEq⟩

/-- **After `lem:dominant-type`: does the dominant root contain an internal
wedge?**  The split is at the one canonical dominant pair node `[431]` fixed;
both arms name it. -/
theorem dominantRootedWedgeType_or_wedgeFree (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (dominantType : DominantRootedTypeSchema data object) :
    DominantRootedWedgeTypeStatement data object ∨
      DominantRootedTypeWedgeFreeStatement data object := by
  classical
  obtain ⟨_rankEq, dominantRoot, canonicalEq⟩ := dominantType
  by_cases wedge : DominantRootWedgeClause object
      (remainderSubcubicSupport data object (canonicalWindowPacking data object))
      dominantRoot.2
  · exact .inl ⟨dominantRoot, canonicalEq, wedge⟩
  · exact .inr ⟨dominantRoot, canonicalEq, wedge⟩

/-- **Nodes `[51]`--`[52]`, `lem:translates-independent`.**  A dominant rooted
radius-two type whose root carries an internal wedge supplies a translated raw
wedge at every dominant centre.  A maximum `2r`-separated set of centres covers
the dominant set by radius-`2r` balls of size at most `b' = 1 + 3(2^{2r}-1)` on
the subcubic support, and its distinct wedges are independent coordinates of
the full-rank remainder, so `|R| ≤ b'·r_Ω(R) + 2T(n)`. -/
theorem independentObstructionTranslates_of_dominantRootedWedgeType
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (cubicBaseline : CubicBaselineStatement data)
    (dominantType : DominantRootedTypeSchema data object)
    (dominantWedge : DominantRootedWedgeTypeStatement data object) :
    IndependentObstructionTranslatesStatement data object := by
  classical
  have cubic : data.threshold = 3 := cubicBaseline.1
  obtain ⟨rankEq, -⟩ := dominantType
  obtain ⟨⟨dominant, root⟩, canonicalEq, rootWedge⟩ := dominantWedge
  obtain ⟨dominantSubset, rootMem, dominantCount, sameType⟩ :=
    canonicalDominantRootedType?_spec_of_eq_some canonicalEq
  let packing := canonicalWindowPacking data object
  let radius := 2
  let support := object.remainderSupport packing
  let subcubic := remainderSubcubicSupport data object packing
  have subcubicSubsetSupport : subcubic ⊆ support := by
    intro vertex member
    exact (Finset.mem_filter.mp member).1
  have dominantSubsetSupport : dominant ⊆ support :=
    dominantSubset.trans subcubicSubsetSupport
  change support.card ≤ dominant.card +
    2 * data.surplusThreshold object.vertexCount at dominantCount
  change support.card ≤
    (1 + data.threshold *
        ((data.threshold - 1) ^ (2 * radius) - 1)) *
      remainderCurvatureTargetRank data object packing +
        2 * data.surplusThreshold object.vertexCount
  have rootedWedges : ∀ vertex ∈ dominant,
      ∃ wedge : object.InternalWedge support,
        wedge.1 = vertex ∧
          wedge ∈ object.internalWedgeFamily support := by
    intro vertex member
    have localWedge :=
      object.rootedInternalWedgeClause_of_code_eq
        subcubic radius
        ⟨root, dominantSubset rootMem⟩
        ⟨vertex, dominantSubset member⟩
        (sameType vertex member) rootWedge
    obtain ⟨wedge, centre, familyMember⟩ := localWedge
    let enlarged := object.internalWedgeOfSubset
      subcubicSubsetSupport wedge
    refine ⟨enlarged, ?_, ?_⟩
    · simpa [enlarged, Graph.FiniteObject.internalWedgeOfSubset] using centre
    · exact object.internalWedgeOfSubset_mem_family
        subcubicSubsetSupport wedge familyMember
  letI : FinEnum object.Vertex :=
    object.vertices
  letI : Fintype object.Vertex := inferInstance
  letI : DecidableEq object.Vertex :=
    object.vertices.decEq
  letI : DecidableRel object.graph.Adj :=
    object.decideAdj
  let ball := fun centre : object.Vertex =>
    Graph.SubcubicReach.reach object.graph subcubic centre
        (2 * radius) centre ∩ subcubic
  have reverseReach : ∀ {left right : object.Vertex},
      left ∈ subcubic → right ∈ subcubic →
        right ∈ ball left → left ∈ ball right := by
    intro left right leftMem rightMem member
    obtain ⟨memberReach, _memberSupport⟩ := Finset.mem_inter.mp member
    obtain ⟨path, pathIsPath, pathLength, pathInside, _pathAvoids⟩ :=
      (Graph.SubcubicReach.mem_reach object.graph).1 memberReach
    apply Finset.mem_inter.mpr
    refine ⟨(Graph.SubcubicReach.mem_reach object.graph).2
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
  have ballSymm : ∀ {left right : object.Vertex},
      left ∈ subcubic → right ∈ subcubic →
        (right ∈ ball left ↔ left ∈ ball right) := by
    intro left right leftMem rightMem
    exact ⟨reverseReach leftMem rightMem, reverseReach rightMem leftMem⟩
  let candidates : Finset (Finset object.Vertex) :=
    dominant.powerset.filter fun selected =>
      (selected : Set object.Vertex).Pairwise
        fun left right => right ∉ ball left
  have candidatesNonempty : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates]
  obtain ⟨selected, selectedMem, maximalSelected⟩ :=
    Finset.exists_max_image candidates Finset.card candidatesNonempty
  have selectedSubset : selected ⊆ dominant :=
    (Finset.mem_filter.mp selectedMem).1 |> Finset.mem_powerset.mp
  have selectedSeparated :
      (selected : Set object.Vertex).Pairwise
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
              object.graph subcubic vertex (2 * radius) vertex,
            dominantSubset vertexMem⟩⟩
    have separatedInsert :
        ((insert vertex selected : Finset object.Vertex) :
            Set object.Vertex).Pairwise
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
      (Graph.SubcubicReach.card_reach_le object.graph
        subcubic (by
          intro vertex member
          change object.degree vertex ≤ 3
          simpa [cubic] using
            (Finset.mem_filter.mp member).2)
        centre (2 * radius))
    simpa [cubic] using
      (Finset.card_le_card Finset.inter_subset_left).trans paperBound
  let smallBall := fun centre : object.Vertex =>
    Graph.SubcubicReach.reach object.graph subcubic centre
        radius centre ∩ subcubic
  have _separatedBalls : ∀ left ∈ selected, ∀ right ∈ selected,
      left ≠ right → Disjoint (smallBall left) (smallBall right) := by
    intro left leftMem right rightMem different
    apply Finset.disjoint_left.mpr
    intro vertex vertexLeft vertexRight
    obtain ⟨leftReach, vertexSupport⟩ := Finset.mem_inter.mp vertexLeft
    obtain ⟨rightReach, _vertexSupport⟩ := Finset.mem_inter.mp vertexRight
    obtain ⟨leftPath, leftIsPath, leftLength, leftInside, _leftAvoids⟩ :=
      (Graph.SubcubicReach.mem_reach object.graph).1 leftReach
    obtain ⟨rightPath, rightIsPath, rightLength, rightInside,
      _rightAvoids⟩ :=
      (Graph.SubcubicReach.mem_reach object.graph).1 rightReach
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
        (reduced : object.graph.Walk left right).length ≤
          2 * radius := by
      calc
        (reduced : object.graph.Walk left right).length ≤
            joined.length :=
          SimpleGraph.Walk.length_bypass_le_length joined
        _ = leftPath.length + rightPath.length := by
          simp [joined, SimpleGraph.Walk.length_append,
            SimpleGraph.Walk.length_reverse]
        _ ≤ radius + radius := Nat.add_le_add leftLength rightLength
        _ = 2 * radius := by omega
    have reducedInside : ∀ member ∈
        (reduced : object.graph.Walk left right).support.dropLast,
        member ∈ subcubic := by
      intro member memberMem
      apply joinedInside member
      exact SimpleGraph.Walk.support_toPath_subset_support joined
        (List.mem_of_mem_dropLast memberMem)
    have reducedAvoids : ∀ notNil :
        ¬ (reduced : object.graph.Walk left right).Nil,
        (reduced : object.graph.Walk left right).getVert 1 ≠
          left := by
      intro notNil same
      have indexZero :=
        (reduced.property.getVert_eq_start_iff_of_not_nil
          (i := 1) notNil).1 same
      exact absurd indexZero (by decide)
    have rightCovered : right ∈ ball left := Finset.mem_inter.mpr ⟨
      (Graph.SubcubicReach.mem_reach object.graph).2
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
      object.InternalWedge support := fun vertex =>
    Classical.choose (rootedWedges vertex.1 (selectedSubset vertex.2))
  have wedgeAtSpec : ∀ vertex : {vertex // vertex ∈ selected},
      (wedgeAt vertex).1 = vertex.1 ∧
        wedgeAt vertex ∈ object.internalWedgeFamily support := by
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
      translates ⊆ object.internalWedgeFamily support := by
    intro wedge wedgeMem
    obtain ⟨vertex, _vertexMem, rfl⟩ := Finset.mem_image.mp wedgeMem
    exact (wedgeAtSpec vertex).2
  have rankEq' : remainderCurvatureTargetRank data object packing =
      object.internalWedgeCount support := by
    simpa only [support, remainderWedgeSupply] using rankEq
  have selectedLeRank : selected.card ≤
      remainderCurvatureTargetRank data object packing := by
    rw [← translatesCard, rankEq',
      ← object.internalWedgeFamily_card support]
    exact Finset.card_le_card translatesSubset
  have dominantLeRank : dominant.card ≤
      (1 + data.threshold *
          ((data.threshold - 1) ^ (2 * radius) - 1)) *
        remainderCurvatureTargetRank data object packing :=
    dominantLe.trans (Nat.mul_le_mul_left _ selectedLeRank)
  omega

end Hypostructure.Graph.Contracts.Spine
