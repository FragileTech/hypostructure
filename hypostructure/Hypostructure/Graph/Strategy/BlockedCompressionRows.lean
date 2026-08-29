import Hypostructure.Graph.Strategy.SpineVocabulary

/-!
# Node `[170]`: `lem:scale-additivity`

`lem:scale-additivity` decides, on the trivial neutral germ residual of node
`[169]` (`K .blockedClassMember`, `def:blocked-class`), whether the conditional
savings of the barrier states add at every fixed scale.  The barrier states
themselves, their completion supports and their conditional fibres are
`Graph/BarrierOverlapSystem.lean`; `W_{a,b}`/`F_{a,b}` are the registered
barrier table's two columns and `c₁₃` its certified `binaryRateFloor`, so no
numeral occurs here.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[170]`: the scale-additivity decision -/

/-- **Node `[170]`, `lem:scale-additivity`**, on the literal `[169]` residual:
either every conditional graph fibre satisfies the denominator-cleared
`F_{a,b}/W_{a,b}` bound, or the no-arm retains the first exposure coordinate,
its fixed outside record and prefix, and the two graph fibres witnessing the
failure.  Constructing the minimal connected overlap support is the next lemma;
it is not smuggled into this decision. -/
noncomputable def scaleAdditivityDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .blockedClassMember) known]
    (additiveFresh : K .blockedScaleAdditive ∉ known)
    (overlapFresh : K .blockedBarrierOverlap ∉ known) :
    Decision (K .blockedScaleAdditive) (K .blockedBarrierOverlap) previous := by
  classical
  let _blocked := (previous.get (K .blockedClassMember)).down
  have safeOfMemberConnector :
      ∀ (member : blockedClassAt data current.object)
        (window : Finset (Fin current.object.vertexCount))
        (windowMem : window ∈ blockedWindowLabels data current.object)
        (presentation : Graph.TypeBDirectCycle.Presentation
          member.1.1.1.toFiniteObject data.windowOrder)
        (supportEq : presentation.support = window)
        (source target : Fin current.object.vertexCount)
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
      (data.lengthOK_iff_powerOfTwo _).2 forbidden
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
    have disjoint : ∀ ⦃z : Fin current.object.vertexCount⦄,
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
      apply data.degenerateClosureRejected
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
  have stateSurvives : ∀ (member : blockedClassAt data current.object)
      (coordinate : blockedCoordinate data current.object),
      IsBlockedSurvivingState data coordinate.2
        ((blockedBarrierCode data current.object member).2 coordinate) := by
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
  have graphFibreMonotone : ∀ coordinate : blockedCoordinate data current.object,
      BlockedGraphFibreMonotonicityAt data current.object coordinate := by
    intro coordinate member₀
    exact Nat.card_le_card_of_injective
      (fun member : BlockedSurvivingConditionalFibre data current.object
          member₀ coordinate ↦
        (⟨member.1, member.2.1⟩ :
          BlockedAprioriConditionalFibre data current.object member₀ coordinate))
      (by
        intro left right equal
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun member :
          BlockedAprioriConditionalFibre data current.object member₀ coordinate ↦
            member.1.1) equal)
  have stateFibreBound : ∀ coordinate : blockedCoordinate data current.object,
      BlockedStateFibreBoundAt data current.object coordinate := by
    intro coordinate member₀
    let labelEmbedding : Fin data.windowBarrier.size →
        {label // label ∈ Graph.WindowCurvature.Labels data.windowOrder} :=
      fun index ↦ ⟨data.windowBarrierLabel index,
        data.windowBarrierLabel_mem index⟩
    have labelEmbeddingBijective : Function.Bijective labelEmbedding := by
      constructor
      · intro left right equal
        apply data.windowBarrierLabel_injective
        exact Subtype.ext_iff.mp equal
      · rintro ⟨label, member⟩
        obtain ⟨index, equal⟩ :=
          data.windowBarrierLabel_surjective label member
        exact ⟨index, Subtype.ext equal⟩
    let labelEquiv := Equiv.ofBijective labelEmbedding labelEmbeddingBijective
    let fibre := Graph.BarrierSystem.ConditionalFibre
      (blockedBarrierCode data current.object)
      (blockedEncodingRank data current.object) member₀ coordinate
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
          have sourceEq : data.windowBarrierLabel sourceIndex = triple.1 :=
            congrArg Subtype.val (labelEquiv.apply_symm_apply
              ⟨triple.1, sourceLegal⟩)
          have middleEq : data.windowBarrierLabel middleIndex = triple.2.1 :=
            congrArg Subtype.val (labelEquiv.apply_symm_apply
              ⟨triple.2.1, middleLegal⟩)
          have targetEq : data.windowBarrierLabel targetIndex = triple.2.2 :=
            congrArg Subtype.val (labelEquiv.apply_symm_apply
              ⟨triple.2.2, targetLegal⟩)
          have leftBit := data.windowBarrier_left_semantic coordinate.2
            sourceIndex middleIndex
          have rightBit := data.windowBarrier_right_semantic coordinate.2
            middleIndex targetIndex
          have sumBit := data.windowBarrier_sum_semantic coordinate.2
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
          (data.windowBarrierLabel triple.1.1,
            data.windowBarrierLabel triple.1.2.1,
            data.windowBarrierLabel triple.1.2.2)
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
  exact Decision.run previous (K .blockedScaleAdditive) (K .blockedBarrierOverlap)
    `Hypostructure.Graph.Strategy.Spine.scaleAdditivityDichotomy
    (if additive : ∀ coordinate : blockedCoordinate data current.object,
        BlockedRelativeFibreBoundAt data current.object coordinate then
      .inl ⟨⟨stateSurvives, fun coordinate ↦
        ⟨stateFibreBound coordinate, graphFibreMonotone coordinate,
          additive coordinate⟩⟩⟩
    else by
      push Not at additive
      let someCoordinate := Classical.choose additive
      have someFailure := Classical.choose_spec additive
      have failedRank : ∃ rank : Nat,
          ∃ coordinate : blockedCoordinate data current.object,
            blockedEncodingRank data current.object coordinate = rank ∧
              ¬ BlockedRelativeFibreBoundAt data current.object coordinate :=
        ⟨blockedEncodingRank data current.object someCoordinate,
          someCoordinate, rfl, someFailure⟩
      let firstCoordinateWitness := Nat.find_spec failedRank
      let firstCoordinate := Classical.choose firstCoordinateWitness
      have firstCoordinateData := Classical.choose_spec firstCoordinateWitness
      have firstFailure :
          ¬ BlockedRelativeFibreBoundAt data current.object firstCoordinate :=
        firstCoordinateData.2
      have failure : BlockedBarrierFailureStatement data current.object := by
        refine ⟨fun coordinate ↦
          ⟨stateFibreBound coordinate, graphFibreMonotone coordinate⟩,
          firstCoordinate, ?_, ?_⟩
        · intro earlier earlierRank
          by_contra earlierFailure
          have firstLeEarlier : Nat.find failedRank ≤
              blockedEncodingRank data current.object earlier :=
            Nat.find_min' failedRank ⟨earlier, rfl, earlierFailure⟩
          have firstRank :
              blockedEncodingRank data current.object firstCoordinate =
                Nat.find failedRank := firstCoordinateData.1
          omega
        · simp only [BlockedRelativeFibreBoundAt] at firstFailure
          push Not at firstFailure
          exact firstFailure
      exact .inr ⟨failure⟩)
    additiveFresh overlapFresh

/-! ## Node `[159]`: the exact dense-packing residual -/

/-- **Node `[159]`, `def:window-realization-test`.**  The no-arm of `[158]`
denies precisely the window-package realization clause.  The identity map on
the labelled skeleton class has range equal to the exact skeleton budget, so
`lem:skeleton-dominates` turns that denial into the manuscript's single strict
display.  The stronger remainder-and-curvature retained code remains solely in
`K .hotColdPartition`; it is not bundled into this node. -/
@[reducible] noncomputable def densePackingOverflowRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.densePackingOverflow
    { Requires := [K .windowPackageUnrealized, K .skeletonDominates]
      Produces := [K .densePackingOverflow]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let unrealized := (inputs.get (K .windowPackageUnrealized)).down
      let dominates := (inputs.get (K .skeletonDominates)).down
      .cons (key := K .densePackingOverflow)
        ⟨by
          classical
          by_contra notDense
          have packageLe :
              2 ^ (windowPackageBits data inputs.current.object *
                (canonicalWindowPacking data inputs.current.object).card) ≤
                Graph.skeletonBudget inputs.current.object :=
            Nat.le_of_not_gt notDense
          apply unrealized
          refine ⟨ULift.{u} (Graph.PackedWindowRealization.Skeleton
            inputs.current.object.vertexCount inputs.current.object.edgeCount),
            ULift.up, ?_⟩
          have range : Nat.card (Set.range (ULift.up.{u} :
              Graph.PackedWindowRealization.Skeleton
                inputs.current.object.vertexCount inputs.current.object.edgeCount → _)) =
              Graph.skeletonBudget inputs.current.object := by
            rw [Set.range_eq_univ.2 (fun state => ⟨state.down, rfl⟩),
              Nat.card_univ, Nat.card_ulift]
            exact dominates.1
          rwa [range]⟩
        .nil)
/-! ## Node `[171]`: `lem:blocked-graphs-compress` -/

set_option maxHeartbeats 800000 in

/-- **Node `[171]`, `lem:blocked-graphs-compress`.**  Expose the exact
near-cubic graph class in the manuscript's canonical scale/window/barrier
order.  The `K .blockedScaleAdditive` ratios multiply over realized prefixes;
the registered barrier table then converts their product into the exact
package-bit saving.  The row publishes both the denominator-cleared
compression inequality and its skeleton-budget consequence. -/
@[reducible] noncomputable def blockedCompressionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.blockedCompression
    { Requires := [K .blockedClassMember, K .blockedScaleAdditive]
      Produces := [K .blockedCompressionBound, K .blockedCompressionCap]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs => by
      let object : Graph.FiniteObject := inputs.current.object
      let blocked := (inputs.get (K .blockedClassMember)).down
      let additive := (inputs.get (K .blockedScaleAdditive)).down
      classical
      letI := data.windowBarrier.indexFintype
      let orderAndRank : {order : blockedCoordinate data object ≃
            Fin (Fintype.card (blockedCoordinate data object)) //
          ∀ coordinate, (order coordinate).1 =
            blockedEncodingRank data object coordinate} := by
        classical
        letI := data.windowBarrier.indexFintype
        have coordinateCard : Fintype.card (blockedCoordinate data object) =
            (data.separatedScaleCount object.vertexCount *
              Fintype.card {window // window ∈ blockedWindowLabels data object}) *
                Fintype.card data.windowBarrier.Index := by
          simp [blockedCoordinate, Graph.BarrierSystem.Coordinate, Nat.mul_comm]
        have rankBound : ∀ coordinate : blockedCoordinate data object,
            blockedEncodingRank data object coordinate <
              Fintype.card (blockedCoordinate data object) := by
          intro coordinate
          rw [coordinateCard]
          exact show blockedEncodingRank data object coordinate <
            (data.separatedScaleCount object.vertexCount *
              Fintype.card {window // window ∈ blockedWindowLabels data object}) *
                Fintype.card data.windowBarrier.Index by
            exact (by
              let rowCount := Fintype.card data.windowBarrier.Index
              let windowCount :=
                Fintype.card {window // window ∈ blockedWindowLabels data object}
              let scaleCount := data.separatedScaleCount object.vertexCount
              have rowLt : (Fintype.equivFin _ coordinate.2).1 < rowCount :=
                (Fintype.equivFin _ coordinate.2).2
              have windowLt : (Fintype.equivFin _ coordinate.1.1).1 < windowCount :=
                (Fintype.equivFin _ coordinate.1.1).2
              have scaleLt : coordinate.1.2.1 < scaleCount := coordinate.1.2.2
              have innerLt :
                  (Fintype.equivFin _ coordinate.1.1).1 +
                      coordinate.1.2.1 * windowCount < scaleCount * windowCount := by
                calc
                  _ < windowCount + coordinate.1.2.1 * windowCount :=
                    Nat.add_lt_add_right windowLt _
                  _ = (coordinate.1.2.1 + 1) * windowCount := by
                    rw [Nat.add_mul, one_mul, Nat.add_comm]
                  _ ≤ scaleCount * windowCount :=
                    Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr scaleLt)
              change (Fintype.equivFin _ coordinate.2).1 +
                  ((Fintype.equivFin _ coordinate.1.1).1 +
                    coordinate.1.2.1 * windowCount) * rowCount < _
              calc
                _ < rowCount +
                      ((Fintype.equivFin _ coordinate.1.1).1 +
                        coordinate.1.2.1 * windowCount) * rowCount :=
                  Nat.add_lt_add_right rowLt _
                _ = (((Fintype.equivFin _ coordinate.1.1).1 +
                        coordinate.1.2.1 * windowCount) + 1) * rowCount := by ring
                _ ≤ (scaleCount * windowCount) * rowCount :=
                  Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr innerLt))
        let rankFin : blockedCoordinate data object →
            Fin (Fintype.card (blockedCoordinate data object)) :=
          fun coordinate ↦ ⟨blockedEncodingRank data object coordinate,
            rankBound coordinate⟩
        have rankFinInjective : Function.Injective rankFin := by
          intro left right equal
          apply blockedEncodingRank_injective data object
          exact Fin.ext_iff.mp equal
        let order := Equiv.ofBijective rankFin
          ((Fintype.bijective_iff_injective_and_card rankFin).2
            ⟨rankFinInjective, by simp⟩)
        have orderRank : ∀ coordinate, (order coordinate).1 =
            blockedEncodingRank data object coordinate := by
          intro coordinate
          rfl
        exact ⟨order, orderRank⟩
      let order := orderAndRank.1
      have orderRank := orderAndRank.2
      have exposure :
          Nat.card (blockedClassAt data object) *
                ∏ coordinate : blockedCoordinate data object,
                  blockedAprioriCountAt data coordinate.2 ≤
            Nat.card (blockedAprioriClassAt data object) *
                ∏ coordinate : blockedCoordinate data object,
                  blockedSurvivingCountAt data coordinate.2 := by
        classical
        letI := data.windowBarrier.indexFintype
        letI : Fintype (blockedClassAt data object) := Fintype.ofFinite _
        letI : Fintype (blockedAprioriClassAt data object) := Fintype.ofFinite _
        let N := Fintype.card (blockedCoordinate data object)
        let Apriori := blockedAprioriClassAt data object
        let Blocked := blockedClassAt data object
        let Outside := Finset (Sym2 (Fin object.vertexCount))
        let BarrierState := Option
          (Graph.WindowCurvature.Label data.windowOrder ×
            Graph.WindowCurvature.Label data.windowOrder ×
              Graph.WindowCurvature.Label data.windowOrder)
        let embed : Blocked → Apriori := fun member ↦ member.1
        have embed_injective : Function.Injective embed :=
          Subtype.val_injective
        let outside : Apriori → Outside := fun member ↦
          (blockedAprioriBarrierCode data object member).1
        let state : Apriori → Fin N → BarrierState := fun member coordinate ↦
          (blockedAprioriBarrierCode data object member).2
            (order.symm coordinate)
        let Survives : Fin N → BarrierState → Prop := fun coordinate value ↦
          IsBlockedSurvivingState data (order.symm coordinate).2 value
        let W : Fin N → Nat := fun coordinate ↦
          blockedAprioriCountAt data (order.symm coordinate).2
        let F : Fin N → Nat := fun coordinate ↦
          blockedSurvivingCountAt data (order.symm coordinate).2
        have blocked_survives : ∀ member coordinate,
            Survives coordinate (state (embed member) coordinate) := by
          intro member coordinate
          simpa [Survives, state, embed, blockedBarrierCode] using
            additive.1 member (order.symm coordinate)
        have local_bound : ∀ (coordinate : Fin N) (member₀ : Blocked),
            W coordinate *
                (Finset.univ.filter fun candidate : Apriori ↦
                  outside candidate = outside (embed member₀) ∧
                  (∀ earlier : Fin N, earlier.1 < coordinate.1 →
                    state candidate earlier = state (embed member₀) earlier) ∧
                  Survives coordinate (state candidate coordinate)).card ≤
              F coordinate *
                (Finset.univ.filter fun candidate : Apriori ↦
                  outside candidate = outside (embed member₀) ∧
                  (∀ earlier : Fin N, earlier.1 < coordinate.1 →
                    state candidate earlier =
                      state (embed member₀) earlier)).card := by
            intro coordinate member₀
            have relative := additive.2 (order.symm coordinate)
            rcases relative with ⟨_stateBound, _monotone, relative⟩
            have relative := relative member₀
            have rankSymm : ∀ index : Fin N,
                blockedEncodingRank data object (order.symm index) = index.1 := by
              intro index
              rw [← orderRank (order.symm index)]
              exact congrArg Fin.val (order.apply_symm_apply index)
            have prefix_iff (candidate : blockedAprioriClassAt data object) :
                (∀ other : blockedCoordinate data object,
                  blockedEncodingRank data object other <
                      blockedEncodingRank data object (order.symm coordinate) →
                    (blockedAprioriBarrierCode data object candidate).2 other =
                      (blockedBarrierCode data object member₀).2 other) ↔
                (∀ earlier : Fin N, earlier.1 < coordinate.1 →
                    (blockedAprioriBarrierCode data object candidate).2
                        (order.symm earlier) =
                      (blockedAprioriBarrierCode data object member₀.1).2
                        (order.symm earlier)) := by
              constructor
              · intro original earlier earlierLt
                simpa [blockedBarrierCode] using original (order.symm earlier)
                  (by simpa [rankSymm] using earlierLt)
              · intro indexed other otherLt
                have earlierLt : (order other).1 < coordinate.1 := by
                  calc
                    (order other).1 = blockedEncodingRank data object other :=
                      orderRank other
                    _ < blockedEncodingRank data object
                          (order.symm coordinate) := otherLt
                    _ = coordinate.1 := rankSymm coordinate
                simpa [blockedBarrierCode] using indexed (order other) earlierLt
            simp only [Nat.card_eq_fintype_card] at relative
            rw [Fintype.card_subtype, Fintype.card_subtype] at relative
            convert relative using 1 <;>
              congr 2 <;>
              ext candidate <;>
              simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                BlockedSurvivingConditionalFibre,
                BlockedAprioriConditionalFibre, Set.mem_setOf_eq,
                blockedBarrierCode] <;>
              rw [← prefix_iff candidate] <;>
              simp [blockedBarrierCode] <;>
              tauto
        have finiteExposure :
            Fintype.card Blocked * ∏ coordinate, W coordinate ≤
              Fintype.card Apriori * ∏ coordinate, F coordinate := by
          classical
          let Prefix : Nat → Type _ := fun k ↦
            Outside × ({coordinate : Fin N // coordinate.1 < k} → BarrierState)
          let record : (∀ k : Nat, Apriori → Prefix k) := fun _ candidate ↦
            (outside candidate, fun coordinate ↦ state candidate coordinate.1)
          let keys : (∀ k : Nat, Finset (Prefix k)) := fun k ↦
            Finset.univ.image fun member : Blocked ↦ record k (embed member)
          let reached : Nat → Finset Apriori := fun k ↦
            Finset.univ.filter fun candidate ↦ record k candidate ∈ keys k
          let Wn : Nat → Nat := fun i ↦ if h : i < N then W ⟨i, h⟩ else 1
          let Fn : Nat → Nat := fun i ↦ if h : i < N then F ⟨i, h⟩ else 1
          have reached_zero_le : (reached 0).card ≤ Fintype.card Apriori := by
            change (reached 0).card ≤ Finset.univ.card
            exact Finset.card_le_card (Finset.filter_subset _ _)
          have blocked_le_reached : Fintype.card Blocked ≤ (reached N).card := by
            change Finset.univ.card ≤ (reached N).card
            refine Finset.card_le_card_of_injOn embed ?_ embed_injective.injOn
            intro member _
            refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
            exact Finset.mem_image.2 ⟨member, Finset.mem_univ _, rfl⟩
          have step : ∀ k (hk : k < N),
              W ⟨k, hk⟩ * (reached (k + 1)).card ≤
                F ⟨k, hk⟩ * (reached k).card := by
            intro k hk
            let coordinate : Fin N := ⟨k, hk⟩
            let before := reached k
            let after := before.filter fun candidate ↦
              Survives coordinate (state candidate coordinate)
            have next_subset : reached (k + 1) ⊆ after := by
              intro candidate candidateMem
              simp only [reached, Finset.mem_filter, Finset.mem_univ, true_and] at candidateMem
              obtain ⟨member, _memberMem, recordEq⟩ :=
                Finset.mem_image.1 candidateMem
              have recordParts :
                  outside (embed member) = outside candidate ∧
                    (∀ earlier : {coordinate : Fin N // coordinate.1 < k + 1},
                      state (embed member) earlier.1 = state candidate earlier.1) := by
                change (outside (embed member), fun earlier :
                    {coordinate : Fin N // coordinate.1 < k + 1} ↦
                      state (embed member) earlier.1) =
                  (outside candidate, fun earlier :
                    {coordinate : Fin N // coordinate.1 < k + 1} ↦
                      state candidate earlier.1) at recordEq
                have parts := Prod.ext_iff.mp recordEq
                exact ⟨parts.1, fun earlier ↦ congrFun parts.2 earlier⟩
              simp only [after, before, Finset.mem_filter]
              constructor
              · simp only [reached, Finset.mem_filter, Finset.mem_univ, true_and]
                refine Finset.mem_image.2 ⟨member, Finset.mem_univ _, ?_⟩
                change
                  (outside (embed member), fun earlier :
                      {coordinate : Fin N // coordinate.1 < k} ↦
                    state (embed member) earlier.1) =
                  (outside candidate, fun earlier :
                      {coordinate : Fin N // coordinate.1 < k} ↦
                    state candidate earlier.1)
                refine Prod.ext_iff.mpr ⟨recordParts.1, ?_⟩
                funext earlier
                exact recordParts.2
                  ⟨earlier.1, lt_trans earlier.2 (Nat.lt_succ_self k)⟩
              · have currentEq := recordParts.2
                  (⟨coordinate, Nat.lt_succ_self k⟩ :
                    {coordinate : Fin N // coordinate.1 < k + 1})
                exact currentEq.symm ▸ blocked_survives member coordinate
            have after_bound : W coordinate * after.card ≤ F coordinate * before.card := by
              let fibreBefore (key : Prefix k) : Finset Apriori :=
                Finset.univ.filter fun candidate ↦ record k candidate = key
              let fibreAfter (key : Prefix k) : Finset Apriori :=
                (fibreBefore key).filter fun candidate ↦
                  Survives coordinate (state candidate coordinate)
              have before_partition : before.card =
                  ∑ key ∈ keys k, (fibreBefore key).card := by
                have partition := Finset.card_eq_sum_card_fiberwise
                  (s := before) (t := keys k) (f := record k) (by
                    intro candidate candidateMem
                    exact (Finset.mem_filter.1 candidateMem).2)
                rw [partition]
                apply Finset.sum_congr rfl
                intro key keyMem
                congr 1
                ext candidate
                simp only [fibreBefore, before, reached, Finset.mem_filter,
                  Finset.mem_univ, true_and]
                constructor
                · intro member
                  exact member.2
                · intro equal
                  have candidateKey : record k candidate ∈ keys k := by
                    rw [equal]
                    exact keyMem
                  exact ⟨candidateKey, equal⟩
              have after_partition : after.card =
                  ∑ key ∈ keys k, (fibreAfter key).card := by
                have partition := Finset.card_eq_sum_card_fiberwise
                  (s := after) (t := keys k) (f := record k) (by
                    intro candidate candidateMem
                    exact (Finset.mem_filter.1 (Finset.mem_filter.1 candidateMem).1).2)
                rw [partition]
                apply Finset.sum_congr rfl
                intro key keyMem
                congr 1
                ext candidate
                simp only [fibreAfter, fibreBefore, after, before, reached,
                  Finset.mem_filter, Finset.mem_univ, true_and]
                constructor
                · intro member
                  exact ⟨member.2, member.1.2⟩
                · intro member
                  have candidateKey : record k candidate ∈ keys k := by
                    rw [member.1]
                    exact keyMem
                  exact ⟨⟨candidateKey, member.2⟩, member.1⟩
              rw [before_partition, after_partition, Finset.mul_sum, Finset.mul_sum]
              apply Finset.sum_le_sum
              intro key keyMem
              obtain ⟨member₀, _memberMem, keyEq⟩ := Finset.mem_image.1 keyMem
              have bound := local_bound coordinate member₀
              have before_eq : (fibreBefore key).card =
                  (Finset.univ.filter fun candidate : Apriori ↦
                    outside candidate = outside (embed member₀) ∧
                    (∀ earlier : Fin N, earlier.1 < coordinate.1 →
                      state candidate earlier = state (embed member₀) earlier)).card := by
                congr 1
                ext candidate
                subst key
                simp only [fibreBefore, Finset.mem_filter, Finset.mem_univ, true_and]
                constructor
                · intro equal
                  have parts := Prod.ext_iff.mp equal
                  refine ⟨parts.1, ?_⟩
                  intro earlier earlierLt
                  exact congrFun parts.2 ⟨earlier, earlierLt⟩
                · rintro ⟨outsideEq, earlierEq⟩
                  change
                    (outside candidate, fun earlier :
                        {coordinate : Fin N // coordinate.1 < k} ↦
                      state candidate earlier.1) =
                    (outside (embed member₀), fun earlier :
                        {coordinate : Fin N // coordinate.1 < k} ↦
                      state (embed member₀) earlier.1)
                  refine Prod.ext_iff.mpr ⟨outsideEq, ?_⟩
                  funext earlier
                  exact earlierEq earlier.1 earlier.2
              have after_eq : (fibreAfter key).card =
                  (Finset.univ.filter fun candidate : Apriori ↦
                    outside candidate = outside (embed member₀) ∧
                    (∀ earlier : Fin N, earlier.1 < coordinate.1 →
                      state candidate earlier = state (embed member₀) earlier) ∧
                    Survives coordinate (state candidate coordinate)).card := by
                congr 1
                ext candidate
                subst key
                simp only [fibreAfter, fibreBefore, Finset.mem_filter,
                  Finset.mem_univ, true_and]
                constructor
                · rintro ⟨equal, survives⟩
                  have parts := Prod.ext_iff.mp equal
                  refine ⟨parts.1, ?_, survives⟩
                  intro earlier earlierLt
                  exact congrFun parts.2 ⟨earlier, earlierLt⟩
                · rintro ⟨outsideEq, earlierEq, survives⟩
                  refine ⟨?_, survives⟩
                  change
                    (outside candidate, fun earlier :
                        {coordinate : Fin N // coordinate.1 < k} ↦
                      state candidate earlier.1) =
                    (outside (embed member₀), fun earlier :
                        {coordinate : Fin N // coordinate.1 < k} ↦
                      state (embed member₀) earlier.1)
                  refine Prod.ext_iff.mpr ⟨outsideEq, ?_⟩
                  funext earlier
                  exact earlierEq earlier.1 earlier.2
              rwa [after_eq, before_eq]
            exact (Nat.mul_le_mul_left _ (Finset.card_le_card next_subset)).trans after_bound
          have accumulated : ∀ k, k ≤ N →
              (reached k).card * ∏ i ∈ Finset.range k, Wn i ≤
                (reached 0).card * ∏ i ∈ Finset.range k, Fn i := by
            intro k hk
            induction k with
            | zero => simp
            | succ k induction =>
                have kLt : k < N := by omega
                have previous := induction (by omega)
                have current := step k kLt
                have Wnk : Wn k = W ⟨k, kLt⟩ := by simp [Wn, kLt]
                have Fnk : Fn k = F ⟨k, kLt⟩ := by simp [Fn, kLt]
                rw [Finset.prod_range_succ, Finset.prod_range_succ]
                calc
                  (reached (k + 1)).card *
                        ((∏ i ∈ Finset.range k, Wn i) * Wn k) =
                      (W ⟨k, kLt⟩ * (reached (k + 1)).card) *
                        ∏ i ∈ Finset.range k, Wn i := by rw [Wnk]; ac_rfl
                  _ ≤ (F ⟨k, kLt⟩ * (reached k).card) *
                        ∏ i ∈ Finset.range k, Wn i :=
                    Nat.mul_le_mul_right _ current
                  _ = F ⟨k, kLt⟩ *
                        ((reached k).card *
                          ∏ i ∈ Finset.range k, Wn i) := by ac_rfl
                  _ ≤ F ⟨k, kLt⟩ *
                        ((reached 0).card *
                          ∏ i ∈ Finset.range k, Fn i) :=
                    Nat.mul_le_mul_left _ previous
                  _ = (reached 0).card *
                        ((∏ i ∈ Finset.range k, Fn i) * Fn k) := by
                    rw [Fnk]; ac_rfl
          have total := accumulated N le_rfl
          have Wprod : (∏ coordinate, W coordinate) = ∏ i ∈ Finset.range N, Wn i := by
            rw [Finset.prod_fin_eq_prod_range]
          have Fprod : (∏ coordinate, F coordinate) = ∏ i ∈ Finset.range N, Fn i := by
            rw [Finset.prod_fin_eq_prod_range]
          rw [Wprod, Fprod]
          calc
            Fintype.card Blocked * ∏ i ∈ Finset.range N, Wn i ≤
                (reached N).card * ∏ i ∈ Finset.range N, Wn i :=
              Nat.mul_le_mul_right _ blocked_le_reached
            _ ≤ (reached 0).card * ∏ i ∈ Finset.range N, Fn i := total
            _ ≤ Fintype.card Apriori * ∏ i ∈ Finset.range N, Fn i :=
              Nat.mul_le_mul_right _ reached_zero_le
        have exposed :
            Fintype.card (blockedClassAt data object) *
                  ∏ coordinate : Fin N,
                    blockedAprioriCountAt data (order.symm coordinate).2 ≤
              Fintype.card (blockedAprioriClassAt data object) *
                  ∏ coordinate : Fin N,
                    blockedSurvivingCountAt data (order.symm coordinate).2 := by
          simpa [Blocked, Apriori, W, F] using finiteExposure
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        have aprioriProd := Fintype.prod_equiv order.symm
          (fun coordinate : Fin N ↦
            blockedAprioriCountAt data (order.symm coordinate).2)
          (fun coordinate : blockedCoordinate data object ↦
            blockedAprioriCountAt data coordinate.2) (by intro; simp)
        have survivingProd := Fintype.prod_equiv order.symm
          (fun coordinate : Fin N ↦
            blockedSurvivingCountAt data (order.symm coordinate).2)
          (fun coordinate : blockedCoordinate data object ↦
            blockedSurvivingCountAt data coordinate.2) (by intro; simp)
        rwa [aprioriProd, survivingProd] at exposed
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
      exact .cons (key := K .blockedCompressionBound) ⟨compressionBound⟩
        (.cons (key := K .blockedCompressionCap) ⟨compressionCap⟩ .nil))

/-- The dense-packing residual is the strict reverse of node `[171]`'s
published terminal budget consequence. -/
noncomputable instance instIncompatibleDensePackingOverflowCompressionCap :
    Incompatible (Input BranchState Presentation presentation data)
      (K .densePackingOverflow) (K .blockedCompressionCap) where
  contradiction := fun _input overflow cap =>
    (Nat.not_lt_of_ge cap.down) overflow.down

/-- Node `[171]` on its additive arm: run the compression producer on the
literal incoming ledger and let Core close its budget cap against node
`[159]`'s strict overflow. -/
noncomputable def blockedCompressionCloses
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .blockedClassMember) known]
    [FactKeys.Has (K .blockedScaleAdditive) known]
    [FactKeys.Has (K .densePackingOverflow) known]
    (boundFresh : K .blockedCompressionBound ∉ known)
    (capFresh : K .blockedCompressionCap ∉ known)
    (closureFresh : closed ∉ known) : False := by
  let closedHistory :=
    (blockedCompressionRow (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data)).runAndCloseIncompatible previous
        (K .densePackingOverflow) (K .blockedCompressionCap)
        (by simp [boundFresh, capFresh])
        (by simp [closureFresh])
  exact closedHistory.elimClosed (by infer_instance)

end Hypostructure.Graph.Strategy.Spine
