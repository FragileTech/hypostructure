import Hypostructure.Graph.Statements.SurplusPair
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle

/-!
# Contract lemmas: the pair-overlap chain `[178]`--`[180]`

`def:pair-overlap-system`, `lem:pair-failure-overlap`, the canonical demand
returns of `lem:pair-system-realizability`, and the power-of-two cycle of
`lem:pair-system-increment-arithmetic`, each over a finite object with the
paper's assumptions as explicit hypotheses.
-/

namespace Hypostructure.Graph.Contracts.SurplusPair

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- Node `[178]` on the full pair schedule of `[131]`: the realized baseline
code and its least failed pair extension, with the failed pair's canonical
connected response support. -/
theorem pairOverlapFirstFailure_of_freeCodeUnrealized
    (unrealized : FreePairCodeUnrealizedStatement data object)
    (noProperBaseline : NoProperBaselineStatement data object) :
    PairOverlapFirstFailureStatement data object := by
  obtain ⟨active, Coordinate, family, coordinateSupport,
      blockerFree, _survives, realizationExists, _demand, _deficitBound,
      _scheduleCard, _countFailure, pairSetNonempty,
      firstFailureExists⟩ :=
    unrealized
  let realization := Classical.choice realizationExists
  let firstFailure := Classical.choice firstFailureExists
  exact ⟨PairOverlapFirstFailure.of data object active
    Coordinate family coordinateSupport realization
    (object.portPairSchedule data.threshold)
    pairSetNonempty (by intro pair member; exact member)
    (by
      intro pair pairMem
      constructor
      · intro obstruction
        exact blockerFree ⟨pair, pairMem, Or.inl obstruction⟩
      · intro obstruction
        exact blockerFree ⟨pair, pairMem, Or.inr obstruction⟩)
    firstFailure
    noProperBaseline.2⟩

/-- Node `[178]` on the capacity-free side of `[137]`: the realized baseline
code and its least failed free-pair extension; every free pair is blocker-free
at the recorded activation. -/
theorem pairOverlapFirstFailure_of_blockedCodeUnrealized
    (unrealized : BlockedPairCodeUnrealizedStatement data object)
    (noProperBaseline : NoProperBaselineStatement data object) :
    PairOverlapFirstFailureStatement data object := by
  obtain ⟨active, capacity, activationEq, _primitiveEq,
      _primitiveLe, _concrete, _scheduleCard, Coordinate, family,
      coordinateSupport, _survives, realizationExists, _demand,
      _deficitBound, _countFailure, pairSetNonempty,
      firstFailureExists⟩ :=
    unrealized
  let pairSet := Graph.freeSide
    object.vertexPairDecidableEq
    (object.portPairSchedule data.threshold)
    capacity.tokenOrder capacity.Eligible capacity.eligibleDecidable
  let realization := Classical.choice realizationExists
  let firstFailure := Classical.choice firstFailureExists
  let activation := Graph.pairResponseActivation active
  let recorded := Graph.recordSparsePairDEBlockers
    (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
    (LengthOK := data.LengthOK) activation
    (object.portPairSchedule data.threshold)
  have pairSetBlockerFree : ∀ pair, pair ∈ pairSet →
      ¬ Graph.SparsePairDEProfileObstructionAt
          (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
          (LengthOK := data.LengthOK) activation
            (object.portPairSchedule data.threshold) pair ∧
        ¬ Graph.SparsePairDEResponseObstructionAt
          (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
          (LengthOK := data.LengthOK) activation
            (object.portPairSchedule data.threshold) pair := by
    intro pair pairMem
    have freeRecorded : pair ∈ capacity.activation.freePairs
        data.threshold :=
      capacity.freeSide_subset_activationFree pairMem
    have freeParts :
        pair ∈ object.portPairSchedule data.threshold ∧
          ¬ (Graph.CanonicalFibreLedger.canonicalLabel
            Graph.SameTokenBlockerRoles.canonicalBlockerOrder
            capacity.activation.Blocks pair).isSome := by
      simpa [Graph.FiniteObject.DemandActivation.freePairs,
        Graph.FiniteObject.freePairs,
        Graph.CanonicalFibreLedger.unassigned] using freeRecorded
    have noRecordedBlocker :
        ¬ (recorded.blockers pair).Nonempty := by
      have noCapacityBlocker :
          ¬ (capacity.activation.blockers pair).Nonempty := by
        intro blocked
        obtain ⟨kind, blocks⟩ :=
          (capacity.activation.exists_blocks_iff_blockers_nonempty
            pair).mpr blocked
        apply freeParts.2
        exact (Graph.CanonicalFibreLedger.isSome_canonicalLabel_iff
          Graph.SameTokenBlockerRoles.canonicalBlockerOrder
          capacity.activation.Blocks pair).mpr
            ⟨kind, capacity.activation.blocks_mem_canonicalBlockerOrder
              blocks, blocks⟩
      simpa [recorded, activation, activationEq] using
        (show ¬ (capacity.activation.blockers pair).Nonempty from
          noCapacityBlocker)
    constructor
    · intro obstruction
      apply noRecordedBlocker
      let coordinate :=
        Graph.FiniteObject.DemandActivation.pairCoordinate pair
          ((activation.pairSupport pair).getD ∅)
      have member : coordinate ∈
          recorded.profileObstructions pair := by
        simp [recorded, Graph.recordSparsePairDEBlockers,
          obstruction, coordinate]
      exact (recorded.exists_blocks_iff_blockers_nonempty pair).mp
        ⟨.boundaryProfile, recorded.blocks_boundaryProfile member⟩
    · intro obstruction
      apply noRecordedBlocker
      let coordinate :=
        Graph.FiniteObject.DemandActivation.pairCoordinate pair
          ((activation.pairSupport pair).getD ∅)
      have member : coordinate ∈
          recorded.responseObstructions pair := by
        simp [recorded, Graph.recordSparsePairDEBlockers,
          obstruction, coordinate]
      exact (recorded.exists_blocks_iff_blockers_nonempty pair).mp
        ⟨.targetResponse, recorded.blocks_targetResponse member⟩
  exact ⟨PairOverlapFirstFailure.of data object active
    Coordinate family coordinateSupport realization pairSet
    pairSetNonempty (by
      intro pair member
      have membership :
          pair ∈ object.portPairSchedule data.threshold ∧
            Graph.CanonicalFibreLedger.canonicalLabel
              capacity.tokenOrder capacity.Eligible pair = none := by
        simpa [pairSet, Graph.freeSide,
          Graph.CanonicalFibreLedger.unassigned] using member
      exact membership.1) pairSetBlockerFree firstFailure
    noProperBaseline.2⟩

/-- Node `[178]`, `def:pair-overlap-system`: the first failure, every
canonical pair support `X_π`, and the literal conditional-fibre overlap system
whose failed family is an obstruction. -/
theorem pairOverlapSystem_of_firstFailure
    (firstFailure : PairOverlapFirstFailureStatement data object)
    (noProperBaseline : NoProperBaselineStatement data object) :
    PairOverlapSystemStatement data object := by
  classical
  let first := Classical.choice
    firstFailure
  let activation := Graph.pairResponseActivation first.active
  let connectedOn :
      Graph.SupportComponents.Connected.ConnectedOn object
        object.vertexFinset :=
    Graph.SupportComponents.Connected.connectedOn_vertexFinset
      object noProperBaseline.2
  let Pair := {pair // pair ∈ first.pairSet}
  have supportExists : ∀ pair : Pair,
      (activation.pairSupport pair.1).isSome := by
    intro pair
    exact activation.pairSupport_isSome_of_connected pair.1 connectedOn
  let responseSupport : Pair → Finset object.Vertex := fun pair =>
    Classical.choose (Option.isSome_iff_exists.mp (supportExists pair))
  have responseSupportSelected : ∀ pair : Pair,
      activation.pairSupport pair.1 = some (responseSupport pair) := by
    intro pair
    exact Classical.choose_spec (Option.isSome_iff_exists.mp
      (supportExists pair))
  have responseSupportConnected : ∀ pair : Pair,
      Graph.SupportComponents.Connected.ConnectedOn object
        (responseSupport pair) := by
    intro pair
    exact (Graph.FiniteObject.DemandActivation.pairSupport_mem_candidates
      (responseSupportSelected pair)).2
  let rank : Pair → Nat := fun pair => first.pairSet.toList.idxOf pair.1
  have rankInjective : Function.Injective rank := by
    intro left right equalRank
    apply Subtype.ext
    exact (List.idxOf_inj (Finset.mem_toList.mpr left.2)).mp equalRank
  let model : Graph.SparsePairSkeletonModel activation
      (object.portPairSchedule data.threshold) :=
    { BaseCoordinate := first.Coordinate
      baselineFamily := first.baselineFamily
      baseline := first.baselineRealization
      pairSet := first.pairSet
      pairSet_nonempty := first.pairSet_nonempty
      pairSet_subset_schedule := first.pairSet_subset_schedule
      responseSupport := responseSupport
      responseSupport_selected := responseSupportSelected
      responseSupport_connected := responseSupportConnected }
  let horizon := first.firstFailure.index + 1
  have horizonLe : horizon ≤ first.pairSet.card := by
    simpa [horizon] using first.firstFailure.index_lt
  let pairAt : Fin horizon → Pair := fun index =>
    ⟨first.pairSet.toList.get
        ⟨index.1, by
          simpa [Finset.length_toList] using
            lt_of_lt_of_le index.2 horizonLe⟩,
      Finset.mem_toList.mp (List.get_mem _ _)⟩
  have pairAtRank : ∀ index : Fin horizon,
      rank (pairAt index) = index.1 := by
    intro index
    dsimp [rank, pairAt]
    exact (Finset.nodup_toList first.pairSet).idxOf_getElem index.1
      (by simpa [Finset.length_toList] using
        lt_of_lt_of_le index.2 horizonLe)
  let failedFamily : Finset Pair :=
    Finset.univ.filter fun pair => rank pair < horizon
  have pairAtMem : ∀ index : Fin horizon, pairAt index ∈ failedFamily := by
    intro index
    simp only [failedFamily, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [pairAtRank index]
    exact index.2
  have rankLt_of_mem_failedFamily : ∀ pair : Pair,
      pair ∈ failedFamily → rank pair < horizon := by
    intro pair member
    change pair ∈ Finset.univ.filter
      (fun candidate => rank candidate < horizon) at member
    exact (Finset.mem_filter.mp member).2
  let prefixEquiv : Fin horizon ≃ {pair // pair ∈ failedFamily} :=
    { toFun := fun index => ⟨pairAt index, pairAtMem index⟩
      invFun := fun pair => ⟨rank pair.1, by
        exact rankLt_of_mem_failedFamily pair.1 pair.2⟩
      left_inv := fun index => by
        apply Fin.ext
        exact pairAtRank index
      right_inv := fun pair => by
        apply Subtype.ext
        apply rankInjective
        exact pairAtRank ⟨rank pair.1, by
          exact rankLt_of_mem_failedFamily pair.1 pair.2⟩ }
  have failedFamilyCard : failedFamily.card = horizon := by
    rw [← Fintype.card_coe]
    calc
      Fintype.card {pair // pair ∈ failedFamily} =
          Fintype.card (Fin horizon) :=
        Fintype.card_congr prefixEquiv.symm
      _ = horizon := Fintype.card_fin horizon
  have failedFamilyNonempty : failedFamily.Nonempty := by
    have horizonPositive : 0 < horizon := by simp [horizon]
    exact Finset.card_pos.mp (by simpa [failedFamilyCard])
  let Skeleton := model.Skeleton
  let Baseline :=
    {coordinate // coordinate ∈ first.baselineFamily} → Bool
  let baselineState : Skeleton → Baseline :=
    fun member => first.baselineRealization.response member.1

  have failedFamilyObstruction : failedFamily.Nonempty ∧
      ¬ model.RealizingOrder (LengthOK := data.LengthOK)
        failedFamily := by
    refine ⟨failedFamilyNonempty, ?_⟩
    rintro ⟨order, realizes⟩
    let coordinateResponse : Skeleton →
        Fin failedFamily.card → PairResponseState data :=
      fun member index =>
        model.response (LengthOK := data.LengthOK) member (order index).1
    have branching : ∀ (index : Fin failedFamily.card)
        (member : Skeleton),
        2 ≤ Nat.card {state // ∃ candidate : Skeleton,
          baselineState candidate = baselineState member ∧
            (∀ earlier : Fin failedFamily.card,
              earlier.1 < index.1 →
                coordinateResponse candidate earlier =
                  coordinateResponse member earlier) ∧
            coordinateResponse candidate index = state} := by
      intro index member
      let Narrow := model.conditionalValues (LengthOK := data.LengthOK)
        failedFamily order member index
      let Broad := {state // ∃ candidate : Skeleton,
        baselineState candidate = baselineState member ∧
          (∀ earlier : Fin failedFamily.card,
            earlier.1 < index.1 →
              coordinateResponse candidate earlier =
                coordinateResponse member earlier) ∧
          coordinateResponse candidate index = state}
      let Candidate := {candidate : Skeleton //
        baselineState candidate = baselineState member ∧
          ∀ earlier : Fin failedFamily.card,
            earlier.1 < index.1 →
              coordinateResponse candidate earlier =
                coordinateResponse member earlier}
      let toBroad : Candidate → Broad := fun candidate =>
        ⟨coordinateResponse candidate.1 index,
          ⟨candidate.1, candidate.2.1, candidate.2.2, rfl⟩⟩
      have toBroadSurjective : Function.Surjective toBroad := by
        intro state
        obtain ⟨candidate, baseEq, earlierEq, responseEq⟩ := state.2
        refine ⟨⟨candidate, baseEq, earlierEq⟩, ?_⟩
        apply Subtype.ext
        exact responseEq
      letI : Finite Candidate := inferInstance
      letI : Finite Broad :=
        Finite.of_surjective toBroad toBroadSurjective
      let narrowToBroad : Narrow → Broad := fun state =>
        ⟨state.1, by
          obtain ⟨candidate, baseEq, earlierEq, responseEq⟩ := state.2
          exact ⟨candidate, baseEq, earlierEq, responseEq⟩⟩
      have narrowToBroadInjective : Function.Injective narrowToBroad := by
        intro left right equal
        apply Subtype.ext
        exact congrArg (fun value : Broad => value.1) equal
      exact (realizes member index).trans
        (Nat.card_le_card_of_injective narrowToBroad
          narrowToBroadInjective)
    have lower : Nat.card Baseline * 2 ^ failedFamily.card ≤
        Nat.card Skeleton := by
      letI : Fintype Skeleton := Fintype.ofFinite Skeleton
      letI : Fintype Baseline := Fintype.ofFinite Baseline
      let signature (length : Nat) (bound : length ≤ failedFamily.card)
          (member : Skeleton) :
          Baseline × (Fin length → PairResponseState data) :=
        (baselineState member, fun index =>
          coordinateResponse member (Fin.castLE bound index))
      let prefixes (length : Nat) (bound : length ≤ failedFamily.card) :
          Finset (Baseline × (Fin length → PairResponseState data)) :=
        Finset.univ.image (signature length bound)
      have baselineSurjective : Function.Surjective baselineState := by
        intro assignment
        obtain ⟨member, realizesAssignment⟩ :=
          first.baselineRealization.realized assignment
        exact ⟨member, realizesAssignment⟩
      have baseCard : Nat.card Baseline ≤
          (prefixes 0 (Nat.zero_le failedFamily.card)).card := by
        have onto : Function.Surjective
            (signature 0 (Nat.zero_le failedFamily.card)) := by
          rintro ⟨value, empty⟩
          obtain ⟨member, memberEq⟩ := baselineSurjective value
          refine ⟨member, ?_⟩
          apply Prod.ext memberEq
          funext index
          exact Fin.elim0 index
        have imageEq : prefixes 0 (Nat.zero_le failedFamily.card) =
            Finset.univ := by
          ext value
          simp only [prefixes, Finset.mem_image, Finset.mem_univ,
            true_and]
          constructor
          · intro _
            trivial
          · intro _
            exact onto value
        rw [imageEq, Finset.card_univ, Nat.card_eq_fintype_card]
        simp
      have step : ∀ length
          (successorBound : length + 1 ≤ failedFamily.card),
          2 * (prefixes length
            (Nat.le_trans (Nat.le_add_right length 1)
              successorBound)).card ≤
            (prefixes (length + 1) successorBound).card := by
        intro length successorBound
        let lengthBound : length ≤ failedFamily.card :=
          Nat.le_trans (Nat.le_add_right length 1) successorBound
        let currentPrefixes := prefixes length lengthBound
        let nextPrefixes := prefixes (length + 1) successorBound
        let project :
            Baseline × (Fin (length + 1) → PairResponseState data) →
              Baseline × (Fin length → PairResponseState data) :=
          fun state => (state.1, fun index => state.2 index.castSucc)
        have mapsTo : Set.MapsTo project ↑nextPrefixes
            ↑currentPrefixes := by
          intro next nextMem
          obtain ⟨member, _, memberEq⟩ := Finset.mem_image.mp nextMem
          subst next
          apply Finset.mem_image.mpr
          refine ⟨member, Finset.mem_univ _, ?_⟩
          apply Prod.ext rfl
          funext index
          rfl
        have fibreTwo : ∀ pref ∈ currentPrefixes,
            2 ≤ {next ∈ nextPrefixes | project next = pref}.card := by
          intro pref prefMem
          obtain ⟨member, _, memberEq⟩ := Finset.mem_image.mp prefMem
          subst pref
          let coordinate : Fin failedFamily.card := ⟨length, by omega⟩
          let Values := {state // ∃ candidate : Skeleton,
            baselineState candidate = baselineState member ∧
              (∀ earlier : Fin failedFamily.card,
                earlier.1 < coordinate.1 →
                  coordinateResponse candidate earlier =
                    coordinateResponse member earlier) ∧
              coordinateResponse candidate coordinate = state}
          have twoValues : 2 ≤ Nat.card Values :=
            branching coordinate member
          have positive : 0 < Nat.card Values :=
            lt_of_lt_of_le (by omega) twoValues
          letI : Finite Values := (Nat.card_pos_iff.mp positive).2
          have notSubsingleton : ¬ Subsingleton Values := by
            intro subsingleton
            have atMostOne : Nat.card Values ≤ 1 :=
              Finite.card_le_one_iff_subsingleton.mpr subsingleton
            omega
          have distinctValues : ∃ left right : Values, left ≠ right := by
            by_contra absent
            push Not at absent
            exact notSubsingleton ⟨absent⟩
          obtain ⟨leftValue, rightValue, valuesDifferent⟩ :=
            distinctValues
          obtain ⟨left, leftBase, leftEarlier, leftResponse⟩ :=
            leftValue.2
          obtain ⟨right, rightBase, rightEarlier, rightResponse⟩ :=
            rightValue.2
          let leftSignature :=
            signature (length + 1) successorBound left
          let rightSignature :=
            signature (length + 1) successorBound right
          have leftMem : leftSignature ∈ nextPrefixes := by
            simp [leftSignature, nextPrefixes, prefixes]
          have rightMem : rightSignature ∈ nextPrefixes := by
            simp [rightSignature, nextPrefixes, prefixes]
          have leftProject : project leftSignature =
              signature length lengthBound member := by
            apply Prod.ext leftBase
            funext index
            apply leftEarlier
            change index.1 < length
            exact index.2
          have rightProject : project rightSignature =
              signature length lengthBound member := by
            apply Prod.ext rightBase
            funext index
            apply rightEarlier
            change index.1 < length
            exact index.2
          have signaturesDifferent : leftSignature ≠ rightSignature := by
            intro equal
            have lastEqual := congrFun (congrArg Prod.snd equal)
              (Fin.last length)
            have lastCoordinate :
                Fin.castLE successorBound (Fin.last length) = coordinate := by
              apply Fin.ext
              rfl
            have responseEqual : coordinateResponse left coordinate =
                coordinateResponse right coordinate := by
              simpa [leftSignature, rightSignature, signature,
                lastCoordinate] using lastEqual
            apply valuesDifferent
            apply Subtype.ext
            exact leftResponse.symm.trans
              (responseEqual.trans rightResponse)
          let chosen : Finset
              (Baseline × (Fin (length + 1) → PairResponseState data)) :=
            {leftSignature, rightSignature}
          have chosenSubset : chosen ⊆
              {next ∈ nextPrefixes |
                project next = signature length lengthBound member} := by
            intro next nextMem
            simp only [chosen, Finset.mem_insert,
              Finset.mem_singleton] at nextMem
            rcases nextMem with rfl | rfl
            · simp [leftMem, leftProject]
            · simp [rightMem, rightProject]
          have chosenCard : chosen.card = 2 := by
            simp [chosen, signaturesDifferent]
          rw [← chosenCard]
          exact Finset.card_le_card chosenSubset
        rw [Finset.card_eq_sum_card_fiberwise mapsTo]
        calc
          2 * currentPrefixes.card =
              ∑ pref ∈ currentPrefixes, 2 := by simp [Nat.mul_comm]
          _ ≤ ∑ pref ∈ currentPrefixes,
              {next ∈ nextPrefixes | project next = pref}.card := by
            gcongr with pref prefMem
            exact fibreTwo pref prefMem
      have prefixGrowth : ∀ length
          (bound : length ≤ failedFamily.card),
          Nat.card Baseline * 2 ^ length ≤
            (prefixes length bound).card := by
        intro length bound
        induction length with
        | zero => simpa using baseCard
        | succ length ih =>
            have previousBound : length ≤ failedFamily.card := by omega
            have doubled := Nat.mul_le_mul_left 2 (ih previousBound)
            have next := step length
              (by simpa [Nat.add_comm] using bound)
            calc
              Nat.card Baseline * 2 ^ (length + 1) =
                  2 * (Nat.card Baseline * 2 ^ length) := by
                rw [pow_succ]
                ac_rfl
              _ ≤ 2 * (prefixes length previousBound).card := doubled
              _ ≤ (prefixes (length + 1) bound).card := by
                simpa [previousBound] using next
      have rangeBound :
          (prefixes failedFamily.card le_rfl).card ≤ Nat.card Skeleton := by
        calc
          (prefixes failedFamily.card le_rfl).card ≤
              (Finset.univ : Finset Skeleton).card :=
            Finset.card_image_le
          _ = Nat.card Skeleton := by
            rw [Finset.card_univ, Nat.card_eq_fintype_card]
      exact (prefixGrowth failedFamily.card le_rfl).trans rangeBound
    have baselineCard : Nat.card Baseline =
        2 ^ first.baselineFamily.card := by
      dsimp [Baseline]
      rw [Nat.card_fun]
      simp [Nat.card_congr first.baselineFamily.equivFin]
    have skeletonCard : Nat.card Skeleton = Graph.skeletonBudget object := by
      dsimp [Skeleton, Graph.SparsePairSkeletonModel.Skeleton]
      simpa [Graph.skeletonBudget, Graph.edgeStratumCount] using
        Graph.PackedWindowRealization.card_skeleton
          object.vertexCount object.edgeCount
    apply first.firstFailure.failedNext
    calc
      2 ^ (first.baselineFamily.card +
            (first.firstFailure.index + 1)) =
          2 ^ first.baselineFamily.card * 2 ^ horizon := by
        rw [pow_add]
      _ = Nat.card Baseline * 2 ^ failedFamily.card := by
        rw [baselineCard, failedFamilyCard]
      _ ≤ Nat.card Skeleton := lower
      _ = Graph.skeletonBudget object := skeletonCard
  let system : PairOverlapSystem data object :=
    { first := first
      responseSupport := responseSupport
      responseSupport_selected := responseSupportSelected
      responseSupport_connected := responseSupportConnected
      rank := rank
      rank_injective := rankInjective
      failedFamily := failedFamily
      failedFamily_eq := rfl
      failedFamily_nonempty := failedFamilyNonempty
      failedFamily_obstruction := by
        simpa [model] using failedFamilyObstruction }
  exact ⟨system⟩

/-- `lem:pair-failure-overlap`, node `[178]`: on a conditionally factorizing
pair overlap system, an inclusion-minimal obstruction inside the failed family
has two overlapping members and a connected union of response supports. -/
theorem pairFailureOverlap_of_factorization
    (factorizationHolds : PairConditionalFactorizationStatement data object) :
    PairFailureOverlapStatement data object := by
  refine ⟨?_⟩
  classical
  let factorizationFact := Classical.choice factorizationHolds
  let system := factorizationFact.1
  have factorization : system.ConditionalFactorization :=
    factorizationFact.2
  let candidates := system.failedFamily.powerset.filter system.obstruction
  have candidatesNonempty : candidates.Nonempty := by
    refine ⟨system.failedFamily, ?_⟩
    simp [candidates, PairOverlapSystem.obstruction,
      PairOverlapSystem.realizingOrder,
      PairOverlapSystem.toSkeletonModel,
      system.failedFamily_nonempty, system.failedFamily_obstruction]
  let selected := candidates.exists_minimal candidatesNonempty
  let family := Classical.choose selected
  have selectedFacts : family ∈ candidates ∧
      ∀ candidate ∈ candidates, candidate ⊆ family →
        family ⊆ candidate := by
    exact Classical.choose_spec selected
  have familyFacts : family ⊆ system.failedFamily ∧
      system.obstruction family := by
    simpa [candidates] using selectedFacts.1
  have minimal : system.minimalObstruction family := by
    refine ⟨familyFacts.2, ?_⟩
    intro proper properSubset properNonempty
    by_contra notRealizing
    have properMem : proper ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨properSubset.subset.trans familyFacts.1,
        ⟨properNonempty, notRealizing⟩⟩
    exact properSubset.2
      (selectedFacts.2 proper properMem properSubset.subset)
  have overlapWitness : ∃ left ∈ family, ∃ right ∈ family,
      left ≠ right ∧ system.toSkeletonModel.Overlaps left right := by
    by_contra absent
    push Not at absent
    have separated : system.toSkeletonModel.PairwiseSeparated family := by
      intro left leftMem right rightMem different overlap
      exact absent left leftMem right rightMem different overlap
    exact minimal.1.2 (factorization.separated family separated)
  have connected :
      Graph.SupportComponents.Connected.ConnectedOn object
        (system.overlapSupport family) := by
    let model := system.toSkeletonModel
    have familyNonempty : family.Nonempty := minimal.1.1
    have notRealizing :
        ¬ model.RealizingOrder (LengthOK := data.LengthOK) family := by
      simpa [model, PairOverlapSystem.realizingOrder] using minimal.1.2
    have properRealizing : ∀ proper, proper ⊂ family → proper.Nonempty →
        model.RealizingOrder (LengthOK := data.LengthOK) proper := by
      intro proper properSubset properNonempty
      simpa [model, PairOverlapSystem.realizingOrder] using
        minimal.2 proper properSubset properNonempty
    let support := model.responseSupportUnion family
    have supportNonempty : support.Nonempty := by
      obtain ⟨pair, pairMem⟩ := familyNonempty
      obtain ⟨vertex, vertexMem⟩ :=
        (model.responseSupport_connected pair).1
      refine ⟨vertex, ?_⟩
      change vertex ∈ model.responseSupportUnion family
      exact Finset.mem_biUnion.mpr ⟨pair, pairMem, vertexMem⟩
    change Graph.SupportComponents.Connected.ConnectedOn object support
    by_contra disconnected
    have componentEqOfPath
        {left right : object.Vertex}
        (leftMem : left ∈ support) (rightMem : right ∈ support)
        (path : object.graph.Walk left right)
        (inside : ∀ vertex ∈ path.support, vertex ∈ support) :
        Graph.SupportComponents.Connected.componentOf object support
            ⟨left, leftMem⟩ =
          Graph.SupportComponents.Connected.componentOf object support
            ⟨right, rightMem⟩ := by
      apply SimpleGraph.ConnectedComponent.sound
      let induced := path.induce (↑support) inside
      exact ⟨by
        simpa [Graph.SupportComponents.Connected.InducedObject,
          Graph.FiniteObject.induce] using induced⟩
    let anchor (pair : {pair // pair ∈ system.first.pairSet}) :
        object.Vertex :=
      Classical.choose (model.responseSupport_connected pair).1
    have anchorMem (pair : {pair // pair ∈ system.first.pairSet}) :
        anchor pair ∈ model.responseSupport pair :=
      Classical.choose_spec (model.responseSupport_connected pair).1
    have responseSubsetOwnComponent
        (pair : {pair // pair ∈ system.first.pairSet})
        (pairMem : pair ∈ family) :
        model.responseSupport pair ⊆
          Graph.SupportComponents.Connected.members object support
            (Graph.SupportComponents.Connected.componentOf object support
              ⟨anchor pair, by
                simpa [support, model, PairOverlapSystem.toSkeletonModel,
                  Graph.SparsePairSkeletonModel.responseSupportUnion] using
                    (Finset.mem_biUnion.mpr
                      ⟨pair, pairMem, anchorMem pair⟩)⟩) := by
      intro vertex vertexMem
      have anchorSupport : anchor pair ∈ support := by
        simpa [support, model, PairOverlapSystem.toSkeletonModel,
          Graph.SparsePairSkeletonModel.responseSupportUnion] using
            (Finset.mem_biUnion.mpr
              ⟨pair, pairMem, anchorMem pair⟩)
      have vertexSupport : vertex ∈ support := by
        simpa [support, model, PairOverlapSystem.toSkeletonModel,
          Graph.SparsePairSkeletonModel.responseSupportUnion] using
            (Finset.mem_biUnion.mpr ⟨pair, pairMem, vertexMem⟩)
      obtain ⟨path, _path, insidePair⟩ :=
        (model.responseSupport_connected pair).2
          (anchorMem pair) vertexMem
      apply (Graph.SupportComponents.Connected.mem_members_iff
        object support _ vertex).mpr
      refine ⟨vertexSupport, ?_⟩
      exact (componentEqOfPath anchorSupport vertexSupport path
        (fun current currentMem => by
          simpa [support, model, PairOverlapSystem.toSkeletonModel,
            Graph.SparsePairSkeletonModel.responseSupportUnion] using
              (Finset.mem_biUnion.mpr
                ⟨pair, pairMem, insidePair current currentMem⟩))).symm
    let rootPair := Classical.choose familyNonempty
    have rootPairMem : rootPair ∈ family :=
      Classical.choose_spec familyNonempty
    have rootAnchorSupport : anchor rootPair ∈ support := by
      simpa [support, model, PairOverlapSystem.toSkeletonModel,
        Graph.SparsePairSkeletonModel.responseSupportUnion] using
          (Finset.mem_biUnion.mpr
            ⟨rootPair, rootPairMem, anchorMem rootPair⟩)
    let rootComponent :=
      Graph.SupportComponents.Connected.componentOf object support
        ⟨anchor rootPair, rootAnchorSupport⟩
    let rootMembers :=
      Graph.SupportComponents.Connected.members object support rootComponent
    have rootComponentMem : rootComponent ∈
        Graph.SupportComponents.Connected.order object support := by
      obtain ⟨component, componentMem, anchorInComponent⟩ :=
        (Graph.SupportComponents.Connected.mem_support_iff_mem_component
          object support (anchor rootPair)).mp rootAnchorSupport
      have equal : rootComponent = component := by
        exact (Graph.SupportComponents.Connected.mem_members_iff
          object support component (anchor rootPair)).mp
            anchorInComponent |>.2
      simpa [equal] using componentMem
    have rootConnected :
        Graph.SupportComponents.Connected.ConnectedOn object rootMembers :=
      Graph.SupportComponents.Connected.connectedOn_of_mem_order
        object support rootComponentMem
    have rootMembersSubset : rootMembers ⊆ support := by
      intro vertex vertexMem
      exact (Graph.SupportComponents.Connected.mem_members_iff
        object support rootComponent vertex).mp vertexMem |>.1
    have rootResponseSubset :
        model.responseSupport rootPair ⊆ rootMembers := by
      simpa [rootComponent, rootMembers] using
        responseSubsetOwnComponent rootPair rootPairMem
    have responseSubsetRootOfCommon
        (pair : {pair // pair ∈ system.first.pairSet})
        (pairMem : pair ∈ family)
        {common : object.Vertex}
        (commonPair : common ∈ model.responseSupport pair)
        (commonRoot : common ∈ rootMembers) :
        model.responseSupport pair ⊆ rootMembers := by
      intro vertex vertexMem
      have commonSupport : common ∈ support :=
        rootMembersSubset commonRoot
      have vertexSupport : vertex ∈ support := by
        simpa [support, model, PairOverlapSystem.toSkeletonModel,
          Graph.SparsePairSkeletonModel.responseSupportUnion] using
            (Finset.mem_biUnion.mpr ⟨pair, pairMem, vertexMem⟩)
      obtain ⟨path, _path, insidePair⟩ :=
        (model.responseSupport_connected pair).2 commonPair vertexMem
      have commonComponent :
          Graph.SupportComponents.Connected.componentOf object support
              ⟨common, commonSupport⟩ = rootComponent :=
        (Graph.SupportComponents.Connected.mem_members_iff
          object support rootComponent common).mp commonRoot |>.2
      have pathComponents :=
        componentEqOfPath commonSupport vertexSupport path
          (fun current currentMem => by
            simpa [support, model, PairOverlapSystem.toSkeletonModel,
              Graph.SparsePairSkeletonModel.responseSupportUnion] using
                (Finset.mem_biUnion.mpr
                  ⟨pair, pairMem, insidePair current currentMem⟩))
      apply (Graph.SupportComponents.Connected.mem_members_iff
        object support rootComponent vertex).mpr
      exact ⟨vertexSupport,
        pathComponents.symm.trans commonComponent⟩
    have outsideRoot : ∃ pair ∈ family,
        ¬ model.responseSupport pair ⊆ rootMembers := by
      by_contra absent
      push Not at absent
      have supportSubset : support ⊆ rootMembers := by
        intro vertex vertexMem
        have inUnion :
            vertex ∈ family.biUnion model.responseSupport := by
          simpa [support, model, PairOverlapSystem.toSkeletonModel,
            Graph.SparsePairSkeletonModel.responseSupportUnion] using
              vertexMem
        obtain ⟨pair, pairMem, inResponse⟩ :=
          Finset.mem_biUnion.mp inUnion
        exact absent pair pairMem inResponse
      have supportEq : support = rootMembers :=
        Finset.Subset.antisymm supportSubset rootMembersSubset
      apply disconnected
      simpa [supportEq] using rootConnected
    let left : Finset {pair // pair ∈ system.first.pairSet} :=
      family.filter fun pair => model.responseSupport pair ⊆ rootMembers
    let right : Finset {pair // pair ∈ system.first.pairSet} :=
      family \ left
    have leftSubset : left ⊆ family := Finset.filter_subset _ _
    have rightSubset : right ⊆ family := Finset.sdiff_subset
    have leftNonempty : left.Nonempty := by
      exact ⟨rootPair, by
        simp [left, rootPairMem, rootResponseSubset]⟩
    have rightNonempty : right.Nonempty := by
      obtain ⟨pair, pairMem, notSubset⟩ := outsideRoot
      exact ⟨pair, by simp [right, left, pairMem, notSubset]⟩
    have disjoint : Disjoint left right := by
      apply Finset.disjoint_left.mpr
      intro pair pairLeft pairRight
      exact (Finset.mem_sdiff.mp pairRight).2 pairLeft
    have noCross : ∀ leftPair, leftPair ∈ left →
        ∀ rightPair, rightPair ∈ right →
          ¬ model.Overlaps leftPair rightPair := by
      intro leftPair leftMem rightPair rightMem overlap
      have leftFacts := Finset.mem_filter.mp leftMem
      have rightFacts := Finset.mem_sdiff.mp rightMem
      obtain ⟨vertex, vertexLeft, vertexRight,
          _leftPort, _rightPort⟩ := overlap
      have rightSubsetRoot := responseSubsetRootOfCommon rightPair
        (rightSubset rightMem) vertexRight (leftFacts.2 vertexLeft)
      exact rightFacts.2 (Finset.mem_filter.mpr
        ⟨rightSubset rightMem, rightSubsetRoot⟩)
    have leftProper : left ⊂ family := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨leftSubset, ?_⟩
      intro equal
      obtain ⟨pair, pairRight⟩ := rightNonempty
      exact (Finset.mem_sdiff.mp pairRight).2
        (equal ▸ rightSubset pairRight)
    have rightProper : right ⊂ family := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨rightSubset, ?_⟩
      intro equal
      obtain ⟨pair, pairLeft⟩ := leftNonempty
      exact (Finset.mem_sdiff.mp
        (equal ▸ leftSubset pairLeft)).2 pairLeft
    have unionEq : left ∪ right = family := by
      change left ∪ (family \ left) = family
      rw [Finset.union_comm]
      exact Finset.sdiff_union_of_subset leftSubset
    apply notRealizing
    have joined := factorization.concatenate left right
      leftNonempty rightNonempty disjoint noCross
      (properRealizing left leftProper leftNonempty)
      (properRealizing right rightProper rightNonempty)
    have familyUnionEq : model.familyUnion left right = family := by
      unfold Graph.SparsePairSkeletonModel.familyUnion
      exact unionEq
    rw [familyUnionEq] at joined
    exact joined
  exact
    { system := system
      family := family
      factorization := factorization
      minimal := minimal
      overlapWitness := overlapWitness
      connected := connected }

/-- Node `[179]`: the two demands of the minimal overlap obstruction with their
canonical port returns and the graph-derived return bound. -/
theorem pairDemandReturns_of_failureOverlap
    (overlap : PairFailureOverlapStatement data object) :
    PairDemandReturnsStatement data object :=
  ⟨PairDemandReturns.of (Classical.choice overlap)⟩

/-- Node `[180]`, direct arithmetic arm (`lem:pair-system-increment-arithmetic`
with `SerialSystem.Spectrum.exists_pow_realized`): the corrected full-modulus
arithmetic realizes an actual simple cycle of length `2^k`, `k ≥ 2`, which is
accepted when the accepted lengths are exactly the powers of two. -/
theorem pairPowerOfTwoCycle_of_arithmetic
    (arithmeticFact : PairSerialArithmeticStatement data object)
    (lengthOK_iff : ∀ length, data.LengthOK length ↔
      Core.DyadicLength.PowerOfTwoLength length) :
    PairPowerOfTwoCycleStatement data object := by
  classical
  let package := Classical.choice
    arithmeticFact
  let serial := package.1
  let arithmetic := Classical.choice package.2
  let spectrum := arithmetic.spectrum
  letI : NeZero arithmetic.modulus := arithmetic.modulus_neZero
  letI : NeZero spectrum.modulus :=
    { out := by
        change arithmetic.modulus ≠ 0
        exact NeZero.ne arithmetic.modulus }
  have spanning : spectrum.ScaleSpanning := by
    simpa [spectrum, PairSerialArithmetic.spectrum] using
      arithmetic.spanning
  let hit := spectrum.exists_pow_realized
    arithmetic.wide arithmetic.criterion spanning
  let exponent := Classical.choose hit
  have realized := Classical.choose_spec hit
  let cycle := Classical.choice realized
  have threeLe : 3 ≤ 2 ^ exponent := by
    rw [← cycle.length_eq]
    exact cycle.isCycle.three_le_length
  have exponentLower : 2 ≤ exponent := by
    by_contra lower
    have cases : exponent = 0 ∨ exponent = 1 := by omega
    rcases cases with zero | one
    · have powerEq : 2 ^ exponent = 1 := by simp [zero]
      omega
    · have powerEq : 2 ^ exponent = 2 := by simp [one]
      omega
  have accepted : data.LengthOK (2 ^ exponent) :=
    (lengthOK_iff (2 ^ exponent)).2
      (Core.DyadicLength.powerOfTwoLength_of_exists
        ⟨exponent, exponentLower, rfl⟩)
  let certificate : Graph.CycleCertificate object
      data.LengthOK :=
    { vertex := cycle.vertex
      walk := cycle.walk
      isCycle := cycle.isCycle
      length_ok := by simpa [cycle.length_eq] using accepted }
  exact ⟨certificate⟩

end Hypostructure.Graph.Contracts.SurplusPair
