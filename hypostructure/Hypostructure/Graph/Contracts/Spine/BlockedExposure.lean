import Hypostructure.Graph.Statements.Spine

/-!
# Contracts: the exposure product of `lem:blocked-graphs-compress` from the aggregate test

The finite exposure counting of `lem:blocked-graphs-compress`, run on the coordinates of
encoding rank below `r` from the aggregate tests of node `[170]`
(`BlockedAggregateBoundAt`).  Nothing else is used: no survival of states, no record.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

set_option maxHeartbeats 1600000 in
/-- **The exposure counting up to rank `r`.**  If the aggregate test holds at every coordinate
of rank below `r`, then `|𝓑(𝒫)|·∏_{rank<r} W ≤ |𝒢_{n,m}|·∏_{rank<r} F`. -/
theorem blockedExposureUpTo (data : Parameters) (object : Graph.FiniteObject.{u})
    (r : Nat) (rle : r ≤ Nat.card (blockedCoordinate data object))
    (aggregate : ∀ coordinate : blockedCoordinate data object,
      blockedEncodingRank data object coordinate < r →
        BlockedAggregateBoundAt data object coordinate) :
    Nat.card (blockedClassAt data object) * blockedPrefixAprioriCount data object r ≤
      Nat.card (blockedAprioriClassAt data object) *
        blockedPrefixSurvivingCount data object r := by
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
  letI : Fintype (blockedClassAt data object) := Fintype.ofFinite _
  letI : Fintype (blockedAprioriClassAt data object) := Fintype.ofFinite _
  let N := Fintype.card (blockedCoordinate data object)
  have rleN : r ≤ N := by
    rw [Nat.card_eq_fintype_card] at rle
    exact rle
  let Apriori := blockedAprioriClassAt data object
  let Blocked := blockedClassAt data object
  let embed : Blocked → Apriori := fun member ↦ member.1
  have embed_injective : Function.Injective embed := Subtype.val_injective
  let outside : Apriori → Finset (Sym2 (Fin object.vertexCount)) := fun member ↦
    (blockedAprioriBarrierCode data object member).1
  let state : Apriori → Fin N → Option (Graph.WindowCurvature.Label data.windowOrder ×
      Graph.WindowCurvature.Label data.windowOrder ×
        Graph.WindowCurvature.Label data.windowOrder) := fun member coordinate ↦
    (blockedAprioriBarrierCode data object member).2 (order.symm coordinate)
  let W : Fin N → Nat := fun coordinate ↦
    blockedAprioriCountAt data (order.symm coordinate).2
  let F : Fin N → Nat := fun coordinate ↦
    blockedSurvivingCountAt data (order.symm coordinate).2
  have rankSymm : ∀ index : Fin N,
      blockedEncodingRank data object (order.symm index) = index.1 := by
    intro index
    rw [← orderRank (order.symm index)]
    exact congrArg Fin.val (order.apply_symm_apply index)
  let reached : Nat → Finset Apriori := fun k ↦
    Finset.univ.filter fun candidate ↦ ∃ member : Blocked,
      outside candidate = outside (embed member) ∧
        ∀ earlier : Fin N, earlier.1 < k →
          state candidate earlier = state (embed member) earlier
  have reachedEq : ∀ k, blockedReachedCount data object k = (reached k).card := by
    intro k
    unfold blockedReachedCount
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext candidate
    simp only [reached, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨member, outsideEq, agree⟩
      refine ⟨member, outsideEq, fun earlier earlierLt ↦ ?_⟩
      exact agree (order.symm earlier) (by rw [rankSymm]; exact earlierLt)
    · rintro ⟨member, outsideEq, agree⟩
      refine ⟨member, outsideEq, fun other otherLt ↦ ?_⟩
      have := agree (order other) (by rw [orderRank]; exact otherLt)
      simpa [state, embed, blockedBarrierCode] using this
  let Wn : Nat → Nat := fun i ↦ if h : i < N then W ⟨i, h⟩ else 1
  let Fn : Nat → Nat := fun i ↦ if h : i < N then F ⟨i, h⟩ else 1
  have reached_zero_le : (reached 0).card ≤ Fintype.card Apriori := by
    change (reached 0).card ≤ Finset.univ.card
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have blocked_le_reached : Fintype.card Blocked ≤ (reached r).card := by
    change Finset.univ.card ≤ (reached r).card
    refine Finset.card_le_card_of_injOn embed ?_ embed_injective.injOn
    intro member _
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, member, rfl, fun _ _ ↦ rfl⟩
  have step : ∀ k (hk : k < N), k < r →
      W ⟨k, hk⟩ * (reached (k + 1)).card ≤ F ⟨k, hk⟩ * (reached k).card := by
    intro k hk hkr
    have bound := aggregate (order.symm ⟨k, hk⟩) (by rw [rankSymm]; exact hkr)
    unfold BlockedAggregateBoundAt at bound
    rw [rankSymm] at bound
    rw [reachedEq, reachedEq] at bound
    exact bound
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
      (fun i hi => (⟨i, lt_of_lt_of_le (Finset.mem_range.1 hi) rleN⟩ : Fin N)) ?_ ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_range.1 hi⟩
    · intro a _ b _ h
      exact congrArg Fin.val h
    · intro j hj
      exact ⟨j.1, Finset.mem_range.2 (Finset.mem_filter.1 hj).2, Fin.ext rfl⟩
    · intro i hi
      have iLt : i < N := lt_of_lt_of_le (Finset.mem_range.1 hi) rleN
      exact dif_pos iLt
  have convF : ∏ i ∈ Finset.range r, Fn i =
      ∏ i ∈ Finset.univ.filter (fun i : Fin N => i.1 < r), F i := by
    refine Finset.prod_bij
      (fun i hi => (⟨i, lt_of_lt_of_le (Finset.mem_range.1 hi) rleN⟩ : Fin N)) ?_ ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_range.1 hi⟩
    · intro a _ b _ h
      exact congrArg Fin.val h
    · intro j hj
      exact ⟨j.1, Finset.mem_range.2 (Finset.mem_filter.1 hj).2, Fin.ext rfl⟩
    · intro i hi
      have iLt : i < N := lt_of_lt_of_le (Finset.mem_range.1 hi) rleN
      exact dif_pos iLt
  rw [convW, convF] at total
  have finite : Fintype.card Blocked *
      ∏ i ∈ Finset.univ.filter (fun i : Fin N => i.1 < r), W i ≤
    Fintype.card Apriori *
      ∏ i ∈ Finset.univ.filter (fun i : Fin N => i.1 < r), F i := by
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
  exact finite


/-- Every encoding rank is below the number of coordinates. -/
theorem blockedRank_lt_card (data : Parameters) (object : Graph.FiniteObject.{u})
    (coordinate : blockedCoordinate data object) :
    blockedEncodingRank data object coordinate < Nat.card (blockedCoordinate data object) := by
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

  have bound := (orderAndRank.1 coordinate).2
  have rankEq := orderAndRank.2 coordinate
  rw [Nat.card_eq_fintype_card]
  omega

/-- **The full exposure product** from the aggregate test at every coordinate:
`|𝓑(𝒫)|·∏W ≤ |𝒢_{n,m}|·∏F`. -/
theorem blockedExposureFull (data : Parameters) (object : Graph.FiniteObject.{u})
    (aggregate : ∀ coordinate : blockedCoordinate data object,
      BlockedAggregateBoundAt data object coordinate) :
    Nat.card (blockedClassAt data object) *
        (letI := data.windowBarrier.indexFintype
         ∏ coordinate : blockedCoordinate data object,
           blockedAprioriCountAt data coordinate.2) ≤
      Nat.card (blockedAprioriClassAt data object) *
        (letI := data.windowBarrier.indexFintype
         ∏ coordinate : blockedCoordinate data object,
           blockedSurvivingCountAt data coordinate.2) := by
  classical
  letI := data.windowBarrier.indexFintype
  have prefixed := blockedExposureUpTo data object
    (Nat.card (blockedCoordinate data object)) le_rfl (fun c _ ↦ aggregate c)
  have allBelow : ∀ coordinate : blockedCoordinate data object,
      coordinate ∈ Finset.univ.filter (fun coordinate : blockedCoordinate data object ↦
        blockedEncodingRank data object coordinate <
          Nat.card (blockedCoordinate data object)) := fun coordinate ↦
    Finset.mem_filter.2 ⟨Finset.mem_univ _, blockedRank_lt_card data object coordinate⟩
  have filterEq : Finset.univ.filter (fun coordinate : blockedCoordinate data object ↦
        blockedEncodingRank data object coordinate <
          Nat.card (blockedCoordinate data object)) = Finset.univ :=
    Finset.eq_univ_of_forall allBelow
  unfold blockedPrefixAprioriCount blockedPrefixSurvivingCount at prefixed
  simp only [filterEq] at prefixed
  exact prefixed

end Hypostructure.Graph.Contracts.Spine
