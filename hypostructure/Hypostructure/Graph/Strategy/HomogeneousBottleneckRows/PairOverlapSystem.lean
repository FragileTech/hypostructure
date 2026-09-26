import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **`def:pair-overlap-system` at node `[178]`.**

Both count-failure routes have already been normalized to the same exact
first-failure key.  This row reads that key and the retained connectivity fact,
selects every canonical pair support `X_π`, and publishes the manuscript's
literal conditional-fibre overlap system. -/
@[reducible] noncomputable def pairOverlapSystemRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairOverlapSystem
    { Requires := [K .pairOverlapFirstFailure, K .noProperBaseline]
      Produces := [K .pairOverlapSystem]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs => by
      classical
      let object := inputs.current.object
      let first := Classical.choice
        (inputs.get (K .pairOverlapFirstFailure)).down
      let activation := Graph.pairResponseActivation first.active
      let connectedOn :
          Graph.SupportComponents.Connected.ConnectedOn object
            object.vertexFinset :=
        Graph.SupportComponents.Connected.connectedOn_vertexFinset
          object (inputs.get (K .noProperBaseline)).down.2
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
            Fin failedFamily.card → PairResponseState data.toParameters :=
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
              Baseline × (Fin length → PairResponseState data.toParameters) :=
            (baselineState member, fun index =>
              coordinateResponse member (Fin.castLE bound index))
          let prefixes (length : Nat) (bound : length ≤ failedFamily.card) :
              Finset (Baseline × (Fin length → PairResponseState data.toParameters)) :=
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
                Baseline × (Fin (length + 1) → PairResponseState data.toParameters) →
                  Baseline × (Fin length → PairResponseState data.toParameters) :=
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
                  (Baseline × (Fin (length + 1) → PairResponseState data.toParameters)) :=
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
      let system : PairOverlapSystem data.toParameters object :=
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
      exact .cons (key := K .pairOverlapSystem)
        (show Value BranchState Presentation presentation data
            .pairOverlapSystem inputs.current from ⟨⟨system⟩⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine
