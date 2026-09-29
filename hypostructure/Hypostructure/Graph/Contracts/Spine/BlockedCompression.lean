import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.Contracts.Spine.BlockedExposure

/-!
# Contracts: the blocked class `[159]`, `[170]`--`[171]`

Proof-agnostic contract lemmas for `def:window-realization-test`'s dense
residual, `lem:scale-additivity` and `lem:blocked-graphs-compress`.  Each lemma
is stated over a `Graph.FiniteObject` with the registered `Parameters` as a
parameter and every paper hypothesis explicit; the registered barrier-row
labelling and its semantic identities, which are presentation data outside
`Parameters`, are explicit hypotheses too.  Its conclusion is exactly the
statement of the fact it proves.  This module imports no strategy, row, or
vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **`lem:scale-additivity`, the surviving barrier state.**  In a blocked
member, every realized barrier state is surviving: each connector between two
attachment labels of a blocked window is safe, since a forbidden (dyadic)
closing length would close an accepted cycle through the window, and the
degenerate closure of length two is rejected. -/
theorem blockedStateSurvives (data : Parameters) (object : Graph.FiniteObject.{u})
    (lengthOK_iff_powerOfTwo : ∀ length,
      data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (degenerateClosureRejected : ¬ data.LengthOK 2) :
    ∀ (member : blockedClassAt data object)
      (coordinate : blockedCoordinate data object),
      IsBlockedSurvivingState data coordinate.2
        ((blockedBarrierCode data object member).2 coordinate) := by
  classical
  have safeOfMemberConnector :
      ∀ (member : blockedClassAt data object)
        (window : Finset (Fin object.vertexCount))
        (windowMem : window ∈ blockedWindowLabels data object)
        (presentation : Graph.TypeBDirectCycle.Presentation
          member.1.1.1.toFiniteObject data.windowOrder)
        (supportEq : presentation.support = window)
        (source target : Fin object.vertexCount)
        (connector : member.1.1.1.graph.Walk source target),
        connector.IsPath →
        (∀ z ∈ connector.support, ∀ t < data.windowOrder,
          z ≠ presentation.coordinate t) →
        Graph.WindowCurvature.Safe connector.length
          (Graph.WindowLabelCollision.attachmentLabel presentation source)
          (Graph.WindowLabelCollision.attachmentLabel presentation target) := by
    intro member window windowMem presentation supportEq source target connector
      connectorPath windowFree
    letI : DecidableEq member.1.1.1.toFiniteObject.Vertex := Classical.decEq _
    intro sourceIndex sourceMem targetIndex targetMem forbidden
    have accepted : data.LengthOK
        (Graph.WindowCurvature.closingLength connector.length
          (Nat.dist sourceIndex.1 targetIndex.1)) :=
      (lengthOK_iff_powerOfTwo _).2 forbidden
    have sourceBound : sourceIndex.1 < data.windowOrder := sourceIndex.2
    have targetBound : targetIndex.1 < data.windowOrder := targetIndex.2
    have enter : member.1.1.1.graph.Adj source
        (presentation.coordinate sourceIndex.1) :=
      Graph.WindowLabelCollision.mem_attachmentLabel.mp sourceMem
    have exiting : member.1.1.1.graph.Adj target
        (presentation.coordinate targetIndex.1) :=
      Graph.WindowLabelCollision.mem_attachmentLabel.mp targetMem
    obtain ⟨stretch, stretchPath, stretchLength, stretchMember⟩ :=
      Graph.TypeBDirectCycle.Presentation.exists_stretch presentation
        (i := sourceIndex.1) (j := targetIndex.1) sourceBound targetBound
    have distEq : stretch.length = Nat.dist sourceIndex.1 targetIndex.1 := by
      rw [stretchLength]
      unfold Nat.dist
      omega
    have disjoint : ∀ ⦃z : Fin object.vertexCount⦄,
        z ∈ stretch.support → z ∉ connector.reverse.support := by
      intro z inStretch inConnector
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at inConnector
      obtain ⟨t, _lower, upper, coordinateEq⟩ := stretchMember _ inStretch
      exact windowFree z inConnector t (by omega) coordinateEq
    have nondegenerate : 0 < stretch.length + connector.reverse.length := by
      by_contra small
      have reverseLength : connector.reverse.length = connector.length := by simp
      have connectorZero : connector.length = 0 := by omega
      have stretchZero : stretch.length = 0 := by omega
      apply degenerateClosureRejected
      have distZero : Nat.dist sourceIndex.1 targetIndex.1 = 0 := by
        rw [← distEq]
        exact stretchZero
      have rewriting : Graph.WindowCurvature.closingLength connector.length
          (Nat.dist sourceIndex.1 targetIndex.1) = 2 := by
        unfold Graph.WindowCurvature.closingLength
        omega
      exact rewriting ▸ accepted
    have acceptedCycle : data.LengthOK
        (stretch.length + connector.reverse.length + 2) := by
      rw [SimpleGraph.Walk.length_reverse, distEq]
      simpa [Graph.WindowCurvature.closingLength, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using accepted
    let certificate := Graph.WindowLabelCollision.connectorCertificate enter
      exiting.symm stretchPath connectorPath.reverse disjoint nondegenerate
      acceptedCycle
    have coordinateMem : presentation.coordinate sourceIndex.1 ∈
        certificate.walk.support := by
      simp [certificate, Graph.WindowLabelCollision.connectorCertificate,
        Graph.WindowLabelCollision.connectorCycle]
    let rotated := certificate.walk.rotate
      (presentation.coordinate sourceIndex.1) coordinateMem
    have rotatedLength : rotated.length = certificate.walk.length := by
      exact SimpleGraph.Walk.length_rotate _ _ _
    apply member.2.blocked window windowMem
    refine ⟨presentation.coordinate sourceIndex.1, ?_, rotated, ?_, ?_⟩
    · rw [← supportEq]
      exact presentation.covers _ sourceBound
    · exact certificate.isCycle.rotate coordinateMem
    · exact rotatedLength.symm ▸ certificate.length_ok
  have stateSurvives : ∀ (member : blockedClassAt data object)
      (coordinate : blockedCoordinate data object),
      IsBlockedSurvivingState data coordinate.2
        ((blockedBarrierCode data object member).2 coordinate) := by
    intro member coordinate
    simp only [blockedBarrierCode, blockedAprioriBarrierCode,
      Graph.BarrierSystem.code]
    unfold Graph.BarrierSystem.barrierState
    split
    next supportExists =>
      let support := supportExists.some
      simp only [IsBlockedSurvivingState]
      have windowMem := coordinate.1.1.2
      have avoidFirst : ∀ z ∈ support.firstArm.support,
          ∀ t < data.windowOrder,
            z ≠ support.presentation.coordinate t := by
        intro z zMem t tBound equal
        apply support.armsOutside z (List.mem_append_left _ zMem)
        subst z
        exact support.presentationInsideInteriors
          (support.presentation.covers t tBound)
      have avoidSecond : ∀ z ∈ support.secondArm.support,
          ∀ t < data.windowOrder,
            z ≠ support.presentation.coordinate t := by
        intro z zMem t tBound equal
        apply support.armsOutside z (List.mem_append_right _ zMem)
        subst z
        exact support.presentationInsideInteriors
          (support.presentation.covers t tBound)
      have avoidComposed : ∀ z ∈
          (support.firstArm.append support.secondArm).support,
          ∀ t < data.windowOrder,
            z ≠ support.presentation.coordinate t := by
        intro z zMem t tBound equal
        rw [SimpleGraph.Walk.support_append] at zMem
        rcases List.mem_append.mp zMem with firstMem | secondMem
        · exact avoidFirst z firstMem t tBound equal
        · exact avoidSecond z (List.mem_of_mem_tail secondMem) t tBound equal
      have safeSource : Graph.WindowCurvature.Safe 0
          (Graph.WindowLabelCollision.attachmentLabel support.presentation
            support.source)
          (Graph.WindowLabelCollision.attachmentLabel support.presentation
            support.source) := by
        simpa using safeOfMemberConnector member coordinate.1.1.1 windowMem
          support.presentation support.presentation_support support.source
          support.source SimpleGraph.Walk.nil SimpleGraph.Walk.IsPath.nil (by
            intro z zMem
            simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at zMem
            subst z
            exact avoidFirst support.source support.firstArm.start_mem_support)
      have safeMiddle : Graph.WindowCurvature.Safe 0
          (Graph.WindowLabelCollision.attachmentLabel support.presentation
            support.middle)
          (Graph.WindowLabelCollision.attachmentLabel support.presentation
            support.middle) := by
        simpa using safeOfMemberConnector member coordinate.1.1.1 windowMem
          support.presentation support.presentation_support support.middle
          support.middle SimpleGraph.Walk.nil SimpleGraph.Walk.IsPath.nil (by
            intro z zMem
            simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at zMem
            subst z
            exact avoidFirst support.middle support.firstArm.end_mem_support)
      have safeTarget : Graph.WindowCurvature.Safe 0
          (Graph.WindowLabelCollision.attachmentLabel support.presentation
            support.target)
          (Graph.WindowLabelCollision.attachmentLabel support.presentation
            support.target) := by
        simpa using safeOfMemberConnector member coordinate.1.1.1 windowMem
          support.presentation support.presentation_support support.target
          support.target SimpleGraph.Walk.nil SimpleGraph.Walk.IsPath.nil (by
            intro z zMem
            simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at zMem
            subst z
            exact avoidSecond support.target support.secondArm.end_mem_support)
      have safeFirst := safeOfMemberConnector member coordinate.1.1.1 windowMem
        support.presentation support.presentation_support support.source
        support.middle support.firstArm support.firstArm_path avoidFirst
      have safeSecond := safeOfMemberConnector member coordinate.1.1.1 windowMem
        support.presentation support.presentation_support support.middle
        support.target support.secondArm support.secondArm_path avoidSecond
      have safeComposed := safeOfMemberConnector member coordinate.1.1.1 windowMem
        support.presentation support.presentation_support support.source
        support.target (support.firstArm.append support.secondArm)
        support.composedArm_path avoidComposed
      refine ⟨Graph.WindowCurvature.mem_Labels.mpr
          ⟨support.sourceIncident, safeSource⟩,
        Graph.WindowCurvature.mem_Labels.mpr
          ⟨support.middleIncident, safeMiddle⟩,
        Graph.WindowCurvature.mem_Labels.mpr
          ⟨support.targetIncident, safeTarget⟩, ?_, ?_, ?_⟩
      · rw [support.firstArm_length] at safeFirst
        simpa [barrierLegs, support] using safeFirst
      · rw [support.secondArm_length] at safeSecond
        simpa [barrierLegs, support] using safeSecond
      · rw [SimpleGraph.Walk.length_append, support.firstArm_length,
          support.secondArm_length] at safeComposed
        simpa [barrierLegs, support] using safeComposed
    next supportMissing => simp [IsBlockedSurvivingState]
  exact stateSurvives

/-- **`lem:scale-additivity`, graph-fibre monotonicity.**  The surviving
conditional fibre injects into the a-priori conditional fibre. -/
theorem blockedGraphFibreMonotone (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    ∀ coordinate : blockedCoordinate data object,
      BlockedGraphFibreMonotonicityAt data object coordinate := by
  classical
  intro coordinate member₀
  exact Nat.card_le_card_of_injective
    (fun member : BlockedSurvivingConditionalFibre data object
        member₀ coordinate ↦
      (⟨member.1, member.2.1⟩ :
        BlockedAprioriConditionalFibre data object member₀ coordinate))
    (by
      intro left right equal
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun member :
        BlockedAprioriConditionalFibre data object member₀ coordinate ↦
          member.1.1) equal)

/-- **`lem:scale-additivity`, the state-fibre bound.**  Surviving barrier
states of a conditional fibre are encoded injectively, through the registered
barrier-row labelling, into the certified flat states of that row, plus the
empty state. -/
theorem blockedStateFibreBound (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (lengthOK_iff_powerOfTwo : ∀ length,
      data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (degenerateClosureRejected : ¬ data.LengthOK 2)
    (windowBarrierLabel : Fin data.windowBarrier.size →
      Graph.WindowCurvature.Label data.windowOrder)
    (windowBarrierLabel_mem : ∀ index,
      windowBarrierLabel index ∈ Graph.WindowCurvature.Labels data.windowOrder)
    (windowBarrierLabel_injective : Function.Injective windowBarrierLabel)
    (windowBarrierLabel_surjective : ∀ label ∈
        Graph.WindowCurvature.Labels data.windowOrder,
      ∃ index, windowBarrierLabel index = label)
    (windowBarrier_left_semantic : ∀ row source target,
      (data.windowBarrier.profile.row
        (data.windowBarrier.table.counts.leftLength row) source).getLsb target =
        decide (Graph.WindowCurvature.Safe
          (data.windowBarrier.table.counts.leftLength row)
          (windowBarrierLabel source) (windowBarrierLabel target)))
    (windowBarrier_right_semantic : ∀ row source target,
      (data.windowBarrier.profile.row
        (data.windowBarrier.table.counts.rightLength row) source).getLsb target =
        decide (Graph.WindowCurvature.Safe
          (data.windowBarrier.table.counts.rightLength row)
          (windowBarrierLabel source) (windowBarrierLabel target)))
    (windowBarrier_sum_semantic : ∀ row source target,
      (data.windowBarrier.profile.row
        (data.windowBarrier.table.counts.leftLength row +
          data.windowBarrier.table.counts.rightLength row) source).getLsb target =
        decide (Graph.WindowCurvature.Safe
          (data.windowBarrier.table.counts.leftLength row +
            data.windowBarrier.table.counts.rightLength row)
          (windowBarrierLabel source) (windowBarrierLabel target))) :
    ∀ coordinate : blockedCoordinate data object,
      BlockedStateFibreBoundAt data object coordinate := by
  classical
  have stateSurvives := blockedStateSurvives data object
    lengthOK_iff_powerOfTwo degenerateClosureRejected
  intro coordinate member₀
  let labelEmbedding : Fin data.windowBarrier.size →
      {label // label ∈ Graph.WindowCurvature.Labels data.windowOrder} :=
    fun index ↦ ⟨windowBarrierLabel index,
      windowBarrierLabel_mem index⟩
  have labelEmbeddingBijective : Function.Bijective labelEmbedding := by
    constructor
    · intro left right equal
      apply windowBarrierLabel_injective
      exact Subtype.ext_iff.mp equal
    · rintro ⟨label, member⟩
      obtain ⟨index, equal⟩ :=
        windowBarrierLabel_surjective label member
      exact ⟨index, Subtype.ext equal⟩
  let labelEquiv := Equiv.ofBijective labelEmbedding labelEmbeddingBijective
  let fibre := Graph.BarrierSystem.ConditionalFibre
    (blockedBarrierCode data object)
    (blockedEncodingRank data object) member₀ coordinate
  have fibreSurvives : ∀ state : fibre,
      IsBlockedSurvivingState data coordinate.2 state.1 := by
    intro state
    obtain ⟨member, _outside, _prefix, equal⟩ := state.2
    exact equal ▸ stateSurvives member coordinate
  let target := Option
    {triple // triple ∈ data.windowBarrier.profile.flatStates
      (data.windowBarrier.table.counts.leftLength coordinate.2)
      (data.windowBarrier.table.counts.rightLength coordinate.2)}
  let encodeState : ∀ state,
      IsBlockedSurvivingState data coordinate.2 state → target :=
    fun state survives ↦ by
    cases state with
    | none => exact none
    | some triple =>
        rcases survives with
          ⟨sourceLegal, middleLegal, targetLegal,
            leftSafe, rightSafe, sumSafe⟩
        let sourceIndex := labelEquiv.symm ⟨triple.1, sourceLegal⟩
        let middleIndex := labelEquiv.symm ⟨triple.2.1, middleLegal⟩
        let targetIndex := labelEquiv.symm ⟨triple.2.2, targetLegal⟩
        refine some ⟨(sourceIndex, middleIndex, targetIndex), ?_⟩
        simp only [Core.FiniteBitRelationBarrier.Profile.flatStates,
          Finset.mem_filter, Finset.mem_univ, true_and]
        have sourceEq : windowBarrierLabel sourceIndex = triple.1 :=
          congrArg Subtype.val (labelEquiv.apply_symm_apply
            ⟨triple.1, sourceLegal⟩)
        have middleEq : windowBarrierLabel middleIndex = triple.2.1 :=
          congrArg Subtype.val (labelEquiv.apply_symm_apply
            ⟨triple.2.1, middleLegal⟩)
        have targetEq : windowBarrierLabel targetIndex = triple.2.2 :=
          congrArg Subtype.val (labelEquiv.apply_symm_apply
            ⟨triple.2.2, targetLegal⟩)
        have leftBit := windowBarrier_left_semantic coordinate.2
          sourceIndex middleIndex
        have rightBit := windowBarrier_right_semantic coordinate.2
          middleIndex targetIndex
        have sumBit := windowBarrier_sum_semantic coordinate.2
          sourceIndex targetIndex
        rw [sourceEq, middleEq, decide_eq_true leftSafe] at leftBit
        rw [middleEq, targetEq, decide_eq_true rightSafe] at rightBit
        rw [sourceEq, targetEq, decide_eq_true sumSafe] at sumBit
        rw [leftBit, rightBit, sumBit]
        rfl
  let encode : fibre → target := fun state ↦
    encodeState state.1 (fibreSurvives state)
  let decode : target → Option
      (Graph.WindowCurvature.Label data.windowOrder ×
        Graph.WindowCurvature.Label data.windowOrder ×
          Graph.WindowCurvature.Label data.windowOrder)
    | none => none
    | some triple => some
        (windowBarrierLabel triple.1.1,
          windowBarrierLabel triple.1.2.1,
          windowBarrierLabel triple.1.2.2)
  have decode_encode : ∀ state : fibre, decode (encode state) = state.1 := by
    rintro ⟨state, stateMember⟩
    cases state with
    | none =>
        have proofEq : fibreSurvives ⟨none, stateMember⟩ = True.intro :=
          Subsingleton.elim _ _
        change decode (encodeState none (fibreSurvives ⟨none, stateMember⟩)) = none
        rw [proofEq]
    | some triple =>
        have survives := fibreSurvives ⟨some triple, stateMember⟩
        rcases survives with
          ⟨sourceLegal, middleLegal, targetLegal,
            leftSafe, rightSafe, sumSafe⟩
        have proofEq : fibreSurvives ⟨some triple, stateMember⟩ =
            ⟨sourceLegal, middleLegal, targetLegal,
              leftSafe, rightSafe, sumSafe⟩ := Subsingleton.elim _ _
        change decode (encodeState (some triple)
          (fibreSurvives ⟨some triple, stateMember⟩)) = some triple
        rw [proofEq]
        simp only [encodeState, decode]
        change some
            ((labelEmbedding (labelEquiv.symm ⟨triple.1, sourceLegal⟩)).1,
              (labelEmbedding
                (labelEquiv.symm ⟨triple.2.1, middleLegal⟩)).1,
              (labelEmbedding
                (labelEquiv.symm ⟨triple.2.2, targetLegal⟩)).1) =
          some triple
        have sourceBack :
            (labelEmbedding (labelEquiv.symm ⟨triple.1, sourceLegal⟩)).1 =
              triple.1 :=
          congrArg Subtype.val (labelEquiv.apply_symm_apply
            ⟨triple.1, sourceLegal⟩)
        have middleBack :
            (labelEmbedding
              (labelEquiv.symm ⟨triple.2.1, middleLegal⟩)).1 =
              triple.2.1 :=
          congrArg Subtype.val (labelEquiv.apply_symm_apply
            ⟨triple.2.1, middleLegal⟩)
        have targetBack :
            (labelEmbedding
              (labelEquiv.symm ⟨triple.2.2, targetLegal⟩)).1 =
              triple.2.2 :=
          congrArg Subtype.val (labelEquiv.apply_symm_apply
            ⟨triple.2.2, targetLegal⟩)
        rw [sourceBack, middleBack, targetBack]
  have encodeInjective : Function.Injective encode := by
    intro left right equal
    apply Subtype.ext
    rw [← decode_encode left, ← decode_encode right, equal]
  calc
    Nat.card fibre ≤ Nat.card target :=
      Nat.card_le_card_of_injective encode encodeInjective
    _ = (data.windowBarrier.profile.flatStates
        (data.windowBarrier.table.counts.leftLength coordinate.2)
        (data.windowBarrier.table.counts.rightLength coordinate.2)).card + 1 := by
      simp [target, Nat.card_eq_fintype_card]
    _ = data.windowBarrier.table.counts.storedFlat coordinate.2 + 1 := by
      rw [data.windowBarrier.profile.card_flatStates]
      exact congrArg (fun count ↦ count + 1)
        (data.windowBarrier.table.counts.flatExact coordinate.2).symm
    _ = blockedSurvivingCountAt data coordinate.2 + 1 := rfl

/-- **Node `[170]`, `lem:scale-additivity`, the additive arm.**  When every
conditional graph fibre satisfies the denominator-cleared `F_{a,b}/W_{a,b}`
bound, the barrier states survive and the state, graph and relative fibre
bounds hold at every coordinate. -/
theorem blockedScaleAdditive_of_aggregate (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (lengthOK_iff_powerOfTwo : ∀ length,
      data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (degenerateClosureRejected : ¬ data.LengthOK 2)
    (windowBarrierLabel : Fin data.windowBarrier.size →
      Graph.WindowCurvature.Label data.windowOrder)
    (windowBarrierLabel_mem : ∀ index,
      windowBarrierLabel index ∈ Graph.WindowCurvature.Labels data.windowOrder)
    (windowBarrierLabel_injective : Function.Injective windowBarrierLabel)
    (windowBarrierLabel_surjective : ∀ label ∈
        Graph.WindowCurvature.Labels data.windowOrder,
      ∃ index, windowBarrierLabel index = label)
    (windowBarrier_left_semantic : ∀ row source target,
      (data.windowBarrier.profile.row
        (data.windowBarrier.table.counts.leftLength row) source).getLsb target =
        decide (Graph.WindowCurvature.Safe
          (data.windowBarrier.table.counts.leftLength row)
          (windowBarrierLabel source) (windowBarrierLabel target)))
    (windowBarrier_right_semantic : ∀ row source target,
      (data.windowBarrier.profile.row
        (data.windowBarrier.table.counts.rightLength row) source).getLsb target =
        decide (Graph.WindowCurvature.Safe
          (data.windowBarrier.table.counts.rightLength row)
          (windowBarrierLabel source) (windowBarrierLabel target)))
    (windowBarrier_sum_semantic : ∀ row source target,
      (data.windowBarrier.profile.row
        (data.windowBarrier.table.counts.leftLength row +
          data.windowBarrier.table.counts.rightLength row) source).getLsb target =
        decide (Graph.WindowCurvature.Safe
          (data.windowBarrier.table.counts.leftLength row +
            data.windowBarrier.table.counts.rightLength row)
          (windowBarrierLabel source) (windowBarrierLabel target)))
    (additive : ∀ coordinate : blockedCoordinate data object,
      BlockedAggregateBoundAt data object coordinate) :
    BlockedScaleAdditivityStatement data object :=
  ⟨blockedStateSurvives data object lengthOK_iff_powerOfTwo
      degenerateClosureRejected,
    fun coordinate ↦
      ⟨blockedStateFibreBound data object lengthOK_iff_powerOfTwo
          degenerateClosureRejected windowBarrierLabel windowBarrierLabel_mem windowBarrierLabel_injective
          windowBarrierLabel_surjective windowBarrier_left_semantic
          windowBarrier_right_semantic windowBarrier_sum_semantic coordinate,
        blockedGraphFibreMonotone data object coordinate,
        additive coordinate⟩⟩

/-- **Node `[170]`, `lem:scale-additivity`, the failure arm.**  When some
conditional graph fibre fails the relative bound, the first failing coordinate
in the canonical encoding order is retained with its failing fibres, together
with the state and graph fibre bounds at every coordinate. -/
theorem blockedBarrierFailure_of_not_aggregate (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (lengthOK_iff_powerOfTwo : ∀ length,
      data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (degenerateClosureRejected : ¬ data.LengthOK 2)
    (windowBarrierLabel : Fin data.windowBarrier.size →
      Graph.WindowCurvature.Label data.windowOrder)
    (windowBarrierLabel_mem : ∀ index,
      windowBarrierLabel index ∈ Graph.WindowCurvature.Labels data.windowOrder)
    (windowBarrierLabel_injective : Function.Injective windowBarrierLabel)
    (windowBarrierLabel_surjective : ∀ label ∈
        Graph.WindowCurvature.Labels data.windowOrder,
      ∃ index, windowBarrierLabel index = label)
    (windowBarrier_left_semantic : ∀ row source target,
      (data.windowBarrier.profile.row
        (data.windowBarrier.table.counts.leftLength row) source).getLsb target =
        decide (Graph.WindowCurvature.Safe
          (data.windowBarrier.table.counts.leftLength row)
          (windowBarrierLabel source) (windowBarrierLabel target)))
    (windowBarrier_right_semantic : ∀ row source target,
      (data.windowBarrier.profile.row
        (data.windowBarrier.table.counts.rightLength row) source).getLsb target =
        decide (Graph.WindowCurvature.Safe
          (data.windowBarrier.table.counts.rightLength row)
          (windowBarrierLabel source) (windowBarrierLabel target)))
    (windowBarrier_sum_semantic : ∀ row source target,
      (data.windowBarrier.profile.row
        (data.windowBarrier.table.counts.leftLength row +
          data.windowBarrier.table.counts.rightLength row) source).getLsb target =
        decide (Graph.WindowCurvature.Safe
          (data.windowBarrier.table.counts.leftLength row +
            data.windowBarrier.table.counts.rightLength row)
          (windowBarrierLabel source) (windowBarrierLabel target)))
    (additive : ¬ ∀ coordinate : blockedCoordinate data object,
      BlockedAggregateBoundAt data object coordinate) :
    BlockedBarrierFailureStatement data object := by
  classical
  have stateFibreBound := blockedStateFibreBound data object
    lengthOK_iff_powerOfTwo degenerateClosureRejected
    windowBarrierLabel windowBarrierLabel_mem windowBarrierLabel_injective
    windowBarrierLabel_surjective windowBarrier_left_semantic
    windowBarrier_right_semantic windowBarrier_sum_semantic
  have graphFibreMonotone := blockedGraphFibreMonotone data object
  push Not at additive
  let someCoordinate := Classical.choose additive
  have someFailure := Classical.choose_spec additive
  have failedRank : ∃ rank : Nat,
      ∃ coordinate : blockedCoordinate data object,
        blockedEncodingRank data object coordinate = rank ∧
          ¬ BlockedAggregateBoundAt data object coordinate :=
    ⟨blockedEncodingRank data object someCoordinate,
      someCoordinate, rfl, someFailure⟩
  let firstCoordinateWitness := Nat.find_spec failedRank
  let firstCoordinate := Classical.choose firstCoordinateWitness
  have firstCoordinateData := Classical.choose_spec firstCoordinateWitness
  have firstFailure :
      ¬ BlockedAggregateBoundAt data object firstCoordinate :=
    firstCoordinateData.2
  have failure : BlockedBarrierFailureStatement data object := by
    refine ⟨firstCoordinate, ?_, ?_⟩
    · intro earlier earlierRank
      by_contra earlierFailure
      have firstLeEarlier : Nat.find failedRank ≤
          blockedEncodingRank data object earlier :=
        Nat.find_min' failedRank ⟨earlier, rfl, earlierFailure⟩
      have firstRank :
          blockedEncodingRank data object firstCoordinate =
            Nat.find failedRank := firstCoordinateData.1
      omega
    · unfold BlockedAggregateBoundAt at firstFailure
      exact not_le.mp firstFailure
  exact failure

set_option maxHeartbeats 800000 in
/-- **Node `[171]`, `lem:blocked-graphs-compress`: the compression bound.**
In the canonical scale/window/barrier order the scale-additive ratios multiply
over realized prefixes, and the registered barrier table converts their
product into the exact package-bit saving. -/
theorem blockedCompressionBound_of_additive (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (additive : BlockedScaleAdditivityStatement data object) :
    BlockedCompressionBoundStatement data object := by
  classical
  letI := data.windowBarrier.indexFintype
  have exposure :
      Nat.card (blockedClassAt data object) *
            ∏ coordinate : blockedCoordinate data object,
              blockedAprioriCountAt data coordinate.2 ≤
        Nat.card (blockedAprioriClassAt data object) *
            ∏ coordinate : blockedCoordinate data object,
              blockedSurvivingCountAt data coordinate.2 :=
    blockedExposureFull data object fun coordinate ↦ (additive.2 coordinate).2.2
  have compressionBound :
      Nat.card (blockedClassAt data object) *
          2 ^ (windowPackageBits data object *
            (canonicalWindowPacking data object).card) ≤
        Nat.card (blockedAprioriClassAt data object) := by
    classical
    letI := data.windowBarrier.indexFintype
    let safe := Core.Finite.CertifiedTableAggregation.safeProduct
      data.windowBarrier.table
    let flat := Core.Finite.CertifiedTableAggregation.flatProduct
      data.windowBarrier.table
    let scales := data.separatedScaleCount object.vertexCount
    let windows := (canonicalWindowPacking data object).card
    let bits := windowPackageBits data object
    have windowLabelsCard : (blockedWindowLabels data object).card = windows := by
      rw [blockedWindowLabels, Graph.BlockedClass.windowLabels,
        Finset.card_image_iff.mpr]
      intro left _ right _ equal
      exact Finset.map_injective _ equal
    have aprioriProduct :
        (∏ coordinate : blockedCoordinate data object,
          blockedAprioriCountAt data coordinate.2) =
          safe ^ (scales * windows) := by
      simpa [safe, scales, windows] using
        (show
          (∏ coordinate : blockedCoordinate data object,
            blockedAprioriCountAt data coordinate.2) =
            Core.Finite.CertifiedTableAggregation.safeProduct
                data.windowBarrier.table ^
              (data.separatedScaleCount object.vertexCount *
                (canonicalWindowPacking data object).card) by
          rw [Fintype.prod_prod_type]
          simp only [blockedAprioriCountAt,
            Core.Finite.CertifiedTableAggregation.safeProduct,
            Core.Finite.CertifiedTableAggregation.product]
          rw [Finset.prod_const]
          simp [Graph.BarrierSystem.Coordinate, Nat.mul_comm,
            windowLabelsCard, windows])
    have survivingProduct :
        (∏ coordinate : blockedCoordinate data object,
          blockedSurvivingCountAt data coordinate.2) =
          flat ^ (scales * windows) := by
      simpa [flat, scales, windows] using
        (show
          (∏ coordinate : blockedCoordinate data object,
            blockedSurvivingCountAt data coordinate.2) =
            Core.Finite.CertifiedTableAggregation.flatProduct
                data.windowBarrier.table ^
              (data.separatedScaleCount object.vertexCount *
                (canonicalWindowPacking data object).card) by
          rw [Fintype.prod_prod_type]
          simp only [blockedSurvivingCountAt,
            Core.Finite.CertifiedTableAggregation.flatProduct,
            Core.Finite.CertifiedTableAggregation.product]
          rw [Finset.prod_const]
          simp [Graph.BarrierSystem.Coordinate, Nat.mul_comm,
            windowLabelsCard, windows])
    have oneWindow : 2 ^ bits * flat ^ scales ≤ safe ^ scales := by
      let quotient := (safe ^ scales - 1) / flat ^ scales
      by_cases quotientZero : quotient = 0
      · have bitsEq : bits = Nat.log2 quotient := rfl
        have bitsZero : bits = 0 := by
          rw [bitsEq, quotientZero]
          rfl
        simpa [bitsZero] using
          Nat.pow_le_pow_left data.windowBarrier.improves scales
      · have powerLe : 2 ^ Nat.log2 quotient ≤ quotient := by
          simpa [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 quotientZero
        calc
          2 ^ bits * flat ^ scales =
              2 ^ Nat.log2 quotient * flat ^ scales := by
            rfl
          _ ≤ quotient * flat ^ scales := Nat.mul_le_mul_right _ powerLe
          _ ≤ safe ^ scales - 1 := Nat.div_mul_le_self _ _
          _ ≤ safe ^ scales := Nat.sub_le _ _
    have rateProduct :
        2 ^ (bits * windows) * (flat ^ scales) ^ windows ≤
          (safe ^ scales) ^ windows := by
      have powered := Nat.pow_le_pow_left oneWindow windows
      rw [mul_pow, ← pow_mul] at powered
      exact powered
    have flatProductPos : 0 < (flat ^ scales) ^ windows :=
      pow_pos (pow_pos data.windowBarrier.flatPositive scales) windows
    rw [aprioriProduct, survivingProduct, pow_mul, pow_mul] at exposure
    have multiplied :
        (Nat.card (blockedClassAt data object) * 2 ^ (bits * windows)) *
            (flat ^ scales) ^ windows ≤
          Nat.card (blockedAprioriClassAt data object) *
            (flat ^ scales) ^ windows := by
      calc
        (Nat.card (blockedClassAt data object) * 2 ^ (bits * windows)) *
              (flat ^ scales) ^ windows =
            Nat.card (blockedClassAt data object) *
              (2 ^ (bits * windows) * (flat ^ scales) ^ windows) := by ac_rfl
        _ ≤ Nat.card (blockedClassAt data object) *
              (safe ^ scales) ^ windows := Nat.mul_le_mul_left _ rateProduct
        _ ≤ Nat.card (blockedAprioriClassAt data object) *
              (flat ^ scales) ^ windows := exposure
    have cancelled := Nat.le_of_mul_le_mul_right multiplied flatProductPos
    simpa [bits, windows] using cancelled
  exact compressionBound

/-- **Node `[171]`, terminal consequence.**  The object's own skeleton is a
member of the blocked class, so the class is nonempty; with the near-cubic
skeleton count the package saving is at most the skeleton budget. -/
theorem blockedCompressionCap_of_bound (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (blocked : BlockedClassMemberStatement data object)
    (compressionBound : BlockedCompressionBoundStatement data object) :
    BlockedCompressionCapStatement data object := by
  classical
  obtain ⟨minDegree, isBlocked, _cardLe⟩ := blocked
  have member : blockedClassAt data object :=
    ⟨⟨Graph.BlockedClass.objectSkeletonMember object, minDegree⟩, isBlocked⟩
  have positive : 0 < Nat.card (blockedClassAt data object) :=
    Nat.pos_of_ne_zero fun zero =>
      (Nat.card_eq_zero.1 zero).elim (fun empty => empty.false member)
        fun infinite => (not_infinite_iff_finite.2 inferInstance) infinite
  have one := Nat.le_mul_of_pos_left
    (2 ^ (windowPackageBits data object *
      (canonicalWindowPacking data object).card)) positive
  have nearCubic := Graph.BlockedClass.card_nearCubicSkeleton_le
    object.vertexCount object.edgeCount data.threshold
  have compressionCap :
      2 ^ (windowPackageBits data object *
          (canonicalWindowPacking data object).card) ≤
        Graph.skeletonBudget object :=
    le_trans (le_trans one compressionBound) nearCubic
  exact compressionCap

end Hypostructure.Graph.Contracts.Spine
