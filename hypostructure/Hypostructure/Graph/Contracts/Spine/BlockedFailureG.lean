import Hypostructure.Graph.Statements.BlockedFailureG
import Hypostructure.Graph.Contracts.Spine.BlockedCompression

/-!
# Contracts: G's own record and the prefix compression at the first failing coordinate of `[170]`

Proof-agnostic contract lemmas for `Statements/BlockedFailureG.lean`.  Hypotheses are the
presentation laws of the registered presentation (the dyadic target and the rejected degenerate
closure), read from `K .cubicBaseline`.  One contract per statement: `<statement>_holds`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

set_option maxHeartbeats 1600000 in
/-- **The prefix compression** (the prefix form of `lem:blocked-graphs-compress`'s finite
exposure).  At any coordinate all of whose predecessors satisfy the cleared `F/W` bound, the
blocked class is compressed by the predecessors alone. -/
theorem blockedPrefixCompression_holds (data : Parameters) (object : Graph.FiniteObject.{u})
    (lengthOK_iff_powerOfTwo : ∀ length,
      data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (degenerateClosureRejected : ¬ data.LengthOK 2) :
    BlockedPrefixCompressionStatement data object := by
  classical
  letI := data.windowBarrier.indexFintype
  intro c₀ prefixBound
  let r := blockedEncodingRank data object c₀
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
  have blockedSurvives := blockedStateSurvives data object lengthOK_iff_powerOfTwo
    degenerateClosureRejected
  have exposure :
      Nat.card (blockedClassAt data object) *
          blockedPrefixAprioriCount data object r ≤
        Nat.card (blockedAprioriClassAt data object) *
          blockedPrefixSurvivingCount data object r := by
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
        blockedSurvives member (order.symm coordinate)
    have local_bound : ∀ (coordinate : Fin N) (member₀ : Blocked), coordinate.1 < r →
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
        intro coordinate member₀ coordinateLt
        have rankSymm : ∀ index : Fin N,
            blockedEncodingRank data object (order.symm index) = index.1 := by
          intro index
          rw [← orderRank (order.symm index)]
          exact congrArg Fin.val (order.apply_symm_apply index)
        have relative := prefixBound (order.symm coordinate)
          (by rw [rankSymm]; exact coordinateLt) member₀
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
    have rLt : r < N := by
      have bound := (order c₀).2
      have rankEq := orderRank c₀
      change blockedEncodingRank data object c₀ < Fintype.card (blockedCoordinate data object)
      omega
    have finiteExposure :
        Fintype.card Blocked *
            ∏ coordinate ∈ Finset.univ.filter (fun i : Fin N => i.1 < r), W coordinate ≤
          Fintype.card Apriori *
            ∏ coordinate ∈ Finset.univ.filter (fun i : Fin N => i.1 < r), F coordinate := by
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
      have blocked_le_reached : Fintype.card Blocked ≤ (reached r).card := by
        change Finset.univ.card ≤ (reached r).card
        refine Finset.card_le_card_of_injOn embed ?_ embed_injective.injOn
        intro member _
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
        exact Finset.mem_image.2 ⟨member, Finset.mem_univ _, rfl⟩
      have step : ∀ k (hk : k < N), k < r →
          W ⟨k, hk⟩ * (reached (k + 1)).card ≤
            F ⟨k, hk⟩ * (reached k).card := by
        intro k hk hkr
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
          have bound := local_bound coordinate member₀ hkr
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
      have accumulated : ∀ k, k ≤ r →
          (reached k).card * ∏ i ∈ Finset.range k, Wn i ≤
            (reached 0).card * ∏ i ∈ Finset.range k, Fn i := by
        intro k hk
        induction k with
        | zero => simp
        | succ k induction =>
            have kLt : k < N := by omega
            have previous := induction (by omega)
            have current := step k kLt (by omega)
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
      have total := accumulated r le_rfl
      have convW : ∏ i ∈ Finset.range r, Wn i =
          ∏ i ∈ Finset.univ.filter (fun i : Fin N => i.1 < r), W i := by
        refine Finset.prod_bij
          (fun i hi => (⟨i, lt_trans (Finset.mem_range.1 hi) rLt⟩ : Fin N)) ?_ ?_ ?_ ?_
        · intro i hi
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_range.1 hi⟩
        · intro a _ b _ h
          exact congrArg Fin.val h
        · intro j hj
          exact ⟨j.1, Finset.mem_range.2 (Finset.mem_filter.1 hj).2, Fin.ext rfl⟩
        · intro i hi
          have iLt : i < N := lt_trans (Finset.mem_range.1 hi) rLt
          exact dif_pos iLt
      have convF : ∏ i ∈ Finset.range r, Fn i =
          ∏ i ∈ Finset.univ.filter (fun i : Fin N => i.1 < r), F i := by
        refine Finset.prod_bij
          (fun i hi => (⟨i, lt_trans (Finset.mem_range.1 hi) rLt⟩ : Fin N)) ?_ ?_ ?_ ?_
        · intro i hi
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_range.1 hi⟩
        · intro a _ b _ h
          exact congrArg Fin.val h
        · intro j hj
          exact ⟨j.1, Finset.mem_range.2 (Finset.mem_filter.1 hj).2, Fin.ext rfl⟩
        · intro i hi
          have iLt : i < N := lt_trans (Finset.mem_range.1 hi) rLt
          exact dif_pos iLt
      rw [convW, convF] at total
      calc
        Fintype.card Blocked *
              ∏ i ∈ Finset.univ.filter (fun i : Fin N => i.1 < r), W i ≤
            (reached r).card *
              ∏ i ∈ Finset.univ.filter (fun i : Fin N => i.1 < r), W i :=
          Nat.mul_le_mul_right _ blocked_le_reached
        _ ≤ (reached 0).card *
              ∏ i ∈ Finset.univ.filter (fun i : Fin N => i.1 < r), F i := total
        _ ≤ Fintype.card Apriori *
              ∏ i ∈ Finset.univ.filter (fun i : Fin N => i.1 < r), F i :=
          Nat.mul_le_mul_right _ reached_zero_le
    have prodW : blockedPrefixAprioriCount data object r =
        ∏ i ∈ Finset.univ.filter (fun i : Fin N => i.1 < r), W i := by
      unfold blockedPrefixAprioriCount
      refine Finset.prod_equiv order ?_ ?_
      · intro c
        exact ⟨fun h ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _, by
            rw [orderRank c]; exact (Finset.mem_filter.1 h).2⟩,
          fun h ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _, by
            have := (Finset.mem_filter.1 h).2
            rw [orderRank c] at this
            exact this⟩⟩
      · intro c _
        show _ = _
        simp only [W, order.symm_apply_apply]
    have prodF : blockedPrefixSurvivingCount data object r =
        ∏ i ∈ Finset.univ.filter (fun i : Fin N => i.1 < r), F i := by
      unfold blockedPrefixSurvivingCount
      refine Finset.prod_equiv order ?_ ?_
      · intro c
        exact ⟨fun h ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _, by
            rw [orderRank c]; exact (Finset.mem_filter.1 h).2⟩,
          fun h ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _, by
            have := (Finset.mem_filter.1 h).2
            rw [orderRank c] at this
            exact this⟩⟩
      · intro c _
        show _ = _
        simp only [F, order.symm_apply_apply]
    rw [prodW, prodF, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact finiteExposure
  exact exposure

/-- **G's own record** (`BlockedOwnRecordStatement`): G's own skeleton, the member of `𝓑(𝒫)`
given by `K .blockedClassMember`, has a surviving barrier state at every coordinate and lies in
both of its own conditional fibres. -/
theorem blockedOwnRecord_holds (data : Parameters) (object : Graph.FiniteObject.{u})
    (lengthOK_iff_powerOfTwo : ∀ length,
      data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (degenerateClosureRejected : ¬ data.LengthOK 2)
    (blocked : BlockedClassMemberStatement data object) :
    BlockedOwnRecordStatement data object := by
  classical
  obtain ⟨minDegree, isBlocked, _cardLe⟩ := blocked
  let own : blockedClassAt data object :=
    ⟨⟨Graph.BlockedClass.objectSkeletonMember object, minDegree⟩, isBlocked⟩
  have survives := blockedStateSurvives data object lengthOK_iff_powerOfTwo
    degenerateClosureRejected
  have monotone := blockedGraphFibreMonotone data object
  refine ⟨own, rfl, fun coordinate ↦ survives own coordinate, fun coordinate ↦ ⟨?_, ?_⟩⟩
  · have member : own.1 ∈ BlockedSurvivingConditionalFibre data object own coordinate :=
      ⟨⟨rfl, fun _ _ ↦ rfl⟩, survives own coordinate⟩
    have nonempty : Nonempty
        (BlockedSurvivingConditionalFibre data object own coordinate) := ⟨⟨own.1, member⟩⟩
    have finite : Finite (BlockedSurvivingConditionalFibre data object own coordinate) :=
      inferInstance
    exact Nat.succ_le_of_lt (Nat.card_pos (α :=
      BlockedSurvivingConditionalFibre data object own coordinate))
  · exact monotone coordinate own

/-- **The strict failure, quantified** (`BlockedFailureSlackStatement`): from the retained
failure of `[170]`. -/
theorem blockedFailureSlack_holds (data : Parameters) (object : Graph.FiniteObject.{u})
    (failure : BlockedBarrierFailureStatement data object) :
    BlockedFailureSlackStatement data object := by
  obtain ⟨_, coordinate, earlier, member₀, strict⟩ := failure
  have monotone := blockedGraphFibreMonotone data object coordinate member₀
  refine ⟨coordinate, earlier, member₀, strict, ?_, monotone, ?_⟩
  · by_contra notPositive
    have zero : Nat.card (BlockedSurvivingConditionalFibre data object member₀
        coordinate) = 0 := Nat.eq_zero_of_not_pos notPositive
    rw [zero, Nat.mul_zero] at strict
    exact Nat.not_lt_zero _ strict
  · by_contra notLess
    have le : blockedAprioriCountAt data coordinate.2 ≤
        blockedSurvivingCountAt data coordinate.2 := Nat.le_of_not_lt notLess
    have chain : blockedAprioriCountAt data coordinate.2 *
          Nat.card (BlockedSurvivingConditionalFibre data object member₀ coordinate) ≤
        blockedSurvivingCountAt data coordinate.2 *
          Nat.card (BlockedAprioriConditionalFibre data object member₀ coordinate) :=
      (Nat.mul_le_mul_right _ le).trans (Nat.mul_le_mul_left _ monotone)
    exact Nat.lt_irrefl _ (strict.trans_le chain)

/-- **The transfer from a comparison record to G** (`BlockedRecordTransferStatement`). -/
theorem blockedRecordTransfer_holds (data : Parameters) (object : Graph.FiniteObject.{u})
    (blocked : BlockedClassMemberStatement data object) :
    BlockedRecordTransferStatement data object := by
  classical
  obtain ⟨minDegree, isBlocked, _cardLe⟩ := blocked
  let own : blockedClassAt data object :=
    ⟨⟨Graph.BlockedClass.objectSkeletonMember object, minDegree⟩, isBlocked⟩
  refine ⟨own, rfl, fun coordinate member₀ outsideEq stateEq ↦ ?_⟩
  have apriori : BlockedAprioriConditionalFibre data object member₀ coordinate =
      BlockedAprioriConditionalFibre data object own coordinate := by
    ext member
    simp only [BlockedAprioriConditionalFibre, Set.mem_setOf_eq]
    rw [outsideEq]
    exact and_congr Iff.rfl (forall_congr' fun other ↦
      imp_congr_right fun lower ↦ by rw [stateEq other lower])
  refine ⟨apriori, ?_⟩
  ext member
  simp only [BlockedSurvivingConditionalFibre, Set.mem_setOf_eq]
  rw [apriori]

/-- **The surviving barrier states of one row are finite and number at most `F_{a,b} + 1`**:
the distinguished absent-completion state and one state per flat triple of the certified
table.  This is the carrier bound `blockedStateFibreBound` uses for a conditional fibre,
for the whole carrier. -/
theorem blockedSurvivingStateCard (data : Parameters)
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
    (row : data.windowBarrier.Index) :
    Finite {state : Option (Graph.WindowCurvature.Label data.windowOrder ×
      Graph.WindowCurvature.Label data.windowOrder ×
        Graph.WindowCurvature.Label data.windowOrder) //
      IsBlockedSurvivingState data row state} ∧
    Nat.card {state : Option (Graph.WindowCurvature.Label data.windowOrder ×
      Graph.WindowCurvature.Label data.windowOrder ×
        Graph.WindowCurvature.Label data.windowOrder) //
      IsBlockedSurvivingState data row state} ≤
      blockedSurvivingCountAt data row + 1 := by
  classical
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
  let fibre := {state : Option (Graph.WindowCurvature.Label data.windowOrder ×
      Graph.WindowCurvature.Label data.windowOrder ×
        Graph.WindowCurvature.Label data.windowOrder) //
    IsBlockedSurvivingState data row state}
  have fibreSurvives : ∀ state : fibre,
      IsBlockedSurvivingState data row state.1 := fun state ↦ state.2
  let target := Option
    {triple // triple ∈ data.windowBarrier.profile.flatStates
      (data.windowBarrier.table.counts.leftLength row)
      (data.windowBarrier.table.counts.rightLength row)}
  let encodeState : ∀ state,
      IsBlockedSurvivingState data row state → target :=
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
        have leftBit := windowBarrier_left_semantic row
          sourceIndex middleIndex
        have rightBit := windowBarrier_right_semantic row
          middleIndex targetIndex
        have sumBit := windowBarrier_sum_semantic row
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
  refine ⟨Finite.of_injective encode encodeInjective, ?_⟩
  calc
    Nat.card fibre ≤ Nat.card target :=
      Nat.card_le_card_of_injective encode encodeInjective
    _ = (data.windowBarrier.profile.flatStates
        (data.windowBarrier.table.counts.leftLength row)
        (data.windowBarrier.table.counts.rightLength row)).card + 1 := by
      simp [target, Nat.card_eq_fintype_card]
    _ = data.windowBarrier.table.counts.storedFlat row + 1 := by
      rw [data.windowBarrier.profile.card_flatStates]
      exact congrArg (fun count ↦ count + 1)
        (data.windowBarrier.table.counts.flatExact row).symm
    _ = blockedSurvivingCountAt data row + 1 := rfl

/-- **The dominant state at the failure** (`BlockedDominantStateStatement`).  The surviving
states of a row number at most `F_{a,b} + 1`, so a surviving graph fibre `S` is covered by at most
`F_{a,b} + 1` state classes of the a-priori fibre `A`; the largest class carries at least
`|S| / (F_{a,b} + 1)` graphs. -/
theorem blockedDominantState_holds (data : Parameters) (object : Graph.FiniteObject.{u})
    (stateCard : ∀ row : data.windowBarrier.Index,
      Finite {state : Option (Graph.WindowCurvature.Label data.windowOrder ×
        Graph.WindowCurvature.Label data.windowOrder ×
          Graph.WindowCurvature.Label data.windowOrder) //
        IsBlockedSurvivingState data row state} ∧
      Nat.card {state : Option (Graph.WindowCurvature.Label data.windowOrder ×
        Graph.WindowCurvature.Label data.windowOrder ×
          Graph.WindowCurvature.Label data.windowOrder) //
        IsBlockedSurvivingState data row state} ≤
        blockedSurvivingCountAt data row + 1) :
    BlockedDominantStateStatement data object := by
  classical
  intro coordinate member₀ strict
  letI : Fintype (blockedAprioriClassAt data object) := Fintype.ofFinite _
  let stateOf : blockedAprioriClassAt data object → Option (Graph.WindowCurvature.Label
      data.windowOrder × Graph.WindowCurvature.Label data.windowOrder ×
        Graph.WindowCurvature.Label data.windowOrder) :=
    fun member ↦ (blockedAprioriBarrierCode data object member).2 coordinate
  let survivors : Finset (blockedAprioriClassAt data object) :=
    Finset.univ.filter fun member ↦
      member ∈ BlockedSurvivingConditionalFibre data object member₀ coordinate
  let apriori : Finset (blockedAprioriClassAt data object) :=
    Finset.univ.filter fun member ↦
      member ∈ BlockedAprioriConditionalFibre data object member₀ coordinate
  have survivorsCard : Nat.card (BlockedSurvivingConditionalFibre data object member₀
      coordinate) = survivors.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have aprioriCard : Nat.card (BlockedAprioriConditionalFibre data object member₀
      coordinate) = apriori.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have survives : ∀ member ∈ survivors,
      IsBlockedSurvivingState data coordinate.2 (stateOf member) := by
    intro member memberMem
    exact (Finset.mem_filter.1 memberMem).2.2
  have positive : 0 < survivors.card := by
    by_contra notPositive
    have zero : Nat.card (BlockedSurvivingConditionalFibre data object member₀
        coordinate) = 0 := by
      rw [survivorsCard]
      exact Nat.eq_zero_of_not_pos notPositive
    rw [zero, Nat.mul_zero] at strict
    exact Nat.not_lt_zero _ strict
  let states : Finset (Option (Graph.WindowCurvature.Label data.windowOrder ×
      Graph.WindowCurvature.Label data.windowOrder ×
        Graph.WindowCurvature.Label data.windowOrder)) := survivors.image stateOf
  have statesNonempty : states.Nonempty := by
    obtain ⟨member, memberMem⟩ := Finset.card_pos.1 positive
    exact ⟨stateOf member, Finset.mem_image_of_mem _ memberMem⟩
  obtain ⟨finiteCarrier, carrierBound⟩ := stateCard coordinate.2
  have statesCard : states.card ≤ blockedSurvivingCountAt data coordinate.2 + 1 := by
    refine le_trans ?_ carrierBound
    have injective : Function.Injective (fun state : states ↦
        (⟨state.1, by
          obtain ⟨member, memberMem, equal⟩ := Finset.mem_image.1 state.2
          exact equal ▸ survives member memberMem⟩ :
          {state // IsBlockedSurvivingState data coordinate.2 state})) := by
      intro left right equal
      have same := congrArg (fun survivor :
        {state // IsBlockedSurvivingState data coordinate.2 state} ↦ survivor.1) equal
      exact Subtype.ext same
    have := Nat.card_le_card_of_injective _ injective
    simpa [Nat.card_eq_fintype_card] using this
  let fibre : Option (Graph.WindowCurvature.Label data.windowOrder ×
      Graph.WindowCurvature.Label data.windowOrder ×
        Graph.WindowCurvature.Label data.windowOrder) → Nat := fun state ↦
    (survivors.filter fun member ↦ stateOf member = state).card
  obtain ⟨best, bestMem, bestMax⟩ := Finset.exists_max_image states fibre statesNonempty
  have partition : survivors.card = ∑ state ∈ states, fibre state :=
    Finset.card_eq_sum_card_fiberwise (f := stateOf) (fun member memberMem ↦
      Finset.mem_image_of_mem _ memberMem)
  have sumLe : ∑ state ∈ states, fibre state ≤ states.card * fibre best := by
    have := Finset.sum_le_card_nsmul states fibre (fibre best) bestMax
    simpa [smul_eq_mul] using this
  have survivorsLe : survivors.card ≤ (blockedSurvivingCountAt data coordinate.2 + 1) *
      fibre best := by
    calc survivors.card = ∑ state ∈ states, fibre state := partition
      _ ≤ states.card * fibre best := sumLe
      _ ≤ (blockedSurvivingCountAt data coordinate.2 + 1) * fibre best :=
        Nat.mul_le_mul_right _ statesCard
  have bestSurvives : IsBlockedSurvivingState data coordinate.2 best := by
    obtain ⟨member, memberMem, equal⟩ := Finset.mem_image.1 bestMem
    exact equal ▸ survives member memberMem
  have fibreLe : fibre best ≤ Nat.card (BlockedStateGraphFibre data object member₀
      coordinate best) := by
    have subset : survivors.filter (fun member ↦ stateOf member = best) ⊆
        Finset.univ.filter (fun member ↦ member ∈ BlockedStateGraphFibre data object
          member₀ coordinate best) := by
      intro member memberMem
      obtain ⟨inSurvivors, hasState⟩ := Finset.mem_filter.1 memberMem
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
        (Finset.mem_filter.1 inSurvivors).2.1, hasState⟩
    have := Finset.card_le_card subset
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact this
  have sLe : Nat.card (BlockedSurvivingConditionalFibre data object member₀ coordinate) ≤
      (blockedSurvivingCountAt data coordinate.2 + 1) *
        Nat.card (BlockedStateGraphFibre data object member₀ coordinate best) := by
    rw [survivorsCard]
    exact survivorsLe.trans (Nat.mul_le_mul_left _ fibreLe)
  exact ⟨best, bestSurvives, sLe, strict.trans_le
    (Nat.mul_le_mul_left _ sLe)⟩

end Hypostructure.Graph.Contracts.Spine
