import Hypostructure.Graph.Statements.BlockedFailureG
import Hypostructure.Graph.Contracts.Spine.BlockedExposure

/-!
# Contracts: the exposure counting with the failing coordinates removed

The general form of `blockedExposureUpTo`: a passing coordinate contributes its aggregate step,
a failing one only the monotonicity `A_{k+1} ≤ A_k`; and the certified package rate.  Together
they give `BlockedFailingSetCarriesStatement`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u


/-- **The certified package rate**: `2^{bits·p}·∏F ≤ ∏W`, with `∏F > 0`. -/
theorem blockedWindowPackageRate (data : Parameters) (object : Graph.FiniteObject.{u}) :
    2 ^ (windowPackageBits data object * (canonicalWindowPacking data object).card) *
        blockedAllSurvivingCount data object ≤ blockedAllAprioriCount data object ∧
      0 < blockedAllSurvivingCount data object := by
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
  unfold blockedAllAprioriCount blockedAllSurvivingCount
  rw [aprioriProduct, survivingProduct, pow_mul flat scales windows, pow_mul safe scales windows]
  exact ⟨rateProduct, flatProductPos⟩

set_option maxHeartbeats 1600000 in
/-- **The exposure counting with the failing coordinates removed.**  A coordinate whose
aggregate test holds contributes `W·A_{k+1} ≤ F·A_k`; a failing one only `A_{k+1} ≤ A_k`.
Hence `|𝓑(𝒫)|·∏_{passing} W ≤ |𝒢_{n,m}|·∏_{passing} F`, with no hypothesis. -/
theorem blockedExposurePassing (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Nat.card (blockedClassAt data object) * blockedPassingAprioriCount data object ≤
      Nat.card (blockedAprioriClassAt data object) *
        blockedPassingSurvivingCount data object := by
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
  let Pass : Fin N → Prop := fun coordinate ↦
    BlockedAggregateBoundAt data object (order.symm coordinate)
  let W : Fin N → Nat := fun coordinate ↦
    if Pass coordinate then blockedAprioriCountAt data (order.symm coordinate).2 else 1
  let F : Fin N → Nat := fun coordinate ↦
    if Pass coordinate then blockedSurvivingCountAt data (order.symm coordinate).2 else 1
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
  have blocked_le_reached : Fintype.card Blocked ≤ (reached N).card := by
    change Finset.univ.card ≤ (reached N).card
    refine Finset.card_le_card_of_injOn embed ?_ embed_injective.injOn
    intro member _
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, member, rfl, fun _ _ ↦ rfl⟩
  have step : ∀ k (hk : k < N),
      W ⟨k, hk⟩ * (reached (k + 1)).card ≤ F ⟨k, hk⟩ * (reached k).card := by
    intro k hk
    by_cases pass : Pass ⟨k, hk⟩
    · have bound : BlockedAggregateBoundAt data object (order.symm ⟨k, hk⟩) := pass
      unfold BlockedAggregateBoundAt at bound
      rw [rankSymm] at bound
      rw [reachedEq, reachedEq] at bound
      simpa [W, F, pass] using bound
    · have subset : reached (k + 1) ⊆ reached k := by
        intro candidate mem
        simp only [reached, Finset.mem_filter, Finset.mem_univ, true_and] at mem ⊢
        obtain ⟨member, outsideEq, agree⟩ := mem
        exact ⟨member, outsideEq, fun earlier lt ↦ agree earlier (Nat.lt_succ_of_lt lt)⟩
      simpa [W, F, pass] using Finset.card_le_card subset
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
  rw [← Wprod, ← Fprod] at total
  have prodW : blockedPassingAprioriCount data object =
      ∏ coordinate, W coordinate := by
    unfold blockedPassingAprioriCount
    rw [Finset.prod_filter]
    refine Fintype.prod_equiv order _ _ ?_
    intro c
    simp only [W, Pass, order.symm_apply_apply]
  have prodF : blockedPassingSurvivingCount data object =
      ∏ coordinate, F coordinate := by
    unfold blockedPassingSurvivingCount
    rw [Finset.prod_filter]
    refine Fintype.prod_equiv order _ _ ?_
    intro c
    simp only [F, Pass, order.symm_apply_apply]
  rw [prodW, prodF, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  calc
    Fintype.card Blocked * ∏ coordinate, W coordinate ≤
        (reached N).card * ∏ coordinate, W coordinate :=
      Nat.mul_le_mul_right _ blocked_le_reached
    _ ≤ (reached 0).card * ∏ coordinate, F coordinate := total
    _ ≤ Fintype.card Apriori * ∏ coordinate, F coordinate :=
      Nat.mul_le_mul_right _ reached_zero_le

/-- **The failing set carries the overflow** (`BlockedFailingSetCarriesStatement`). -/
theorem blockedFailingSetCarries_holds (data : Parameters) (object : Graph.FiniteObject.{u}) :
    BlockedFailingSetCarriesStatement data object := by
  classical
  letI := data.windowBarrier.indexFintype
  obtain ⟨rate, positive⟩ := blockedWindowPackageRate data object
  have passing := blockedExposurePassing data object
  have splitW : blockedAllAprioriCount data object =
      blockedPassingAprioriCount data object * blockedFailingAprioriCount data object := by
    unfold blockedAllAprioriCount blockedPassingAprioriCount blockedFailingAprioriCount
    exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  have splitF : blockedAllSurvivingCount data object =
      blockedPassingSurvivingCount data object * blockedFailingSurvivingCount data object := by
    unfold blockedAllSurvivingCount blockedPassingSurvivingCount blockedFailingSurvivingCount
    exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  rw [splitW, splitF] at rate
  rw [splitF] at positive
  have passingPos : 0 < blockedPassingSurvivingCount data object :=
    Nat.pos_of_ne_zero fun zero ↦ by
      rw [zero, Nat.zero_mul] at positive
      exact Nat.lt_irrefl _ positive
  unfold BlockedFailingSetCarriesStatement
  refine Nat.le_of_mul_le_mul_right ?_ passingPos
  calc
    Nat.card (blockedClassAt data object) *
          2 ^ (windowPackageBits data object *
            (canonicalWindowPacking data object).card) *
          blockedFailingSurvivingCount data object *
        blockedPassingSurvivingCount data object =
        Nat.card (blockedClassAt data object) *
          (2 ^ (windowPackageBits data object *
              (canonicalWindowPacking data object).card) *
            (blockedPassingSurvivingCount data object *
              blockedFailingSurvivingCount data object)) := by ac_rfl
    _ ≤ Nat.card (blockedClassAt data object) *
          (blockedPassingAprioriCount data object * blockedFailingAprioriCount data object) :=
      Nat.mul_le_mul_left _ rate
    _ = (Nat.card (blockedClassAt data object) * blockedPassingAprioriCount data object) *
          blockedFailingAprioriCount data object := by ac_rfl
    _ ≤ (Nat.card (blockedAprioriClassAt data object) *
          blockedPassingSurvivingCount data object) * blockedFailingAprioriCount data object :=
      Nat.mul_le_mul_right _ passing
    _ = Nat.card (blockedAprioriClassAt data object) *
          blockedFailingAprioriCount data object * blockedPassingSurvivingCount data object := by
      ac_rfl

end Hypostructure.Graph.Contracts.Spine
