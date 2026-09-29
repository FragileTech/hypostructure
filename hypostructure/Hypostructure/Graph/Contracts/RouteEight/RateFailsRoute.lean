import Hypostructure.Graph.Contracts.RouteEight.RateFailsAccounting
import Hypostructure.Graph.Contracts.RouteEight.Collection
import Hypostructure.Graph.Statements.Route8RateFailsRoute

/-!
# Contracts: empty or determined cores, the strong rate, the thin remainder
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open scoped BigOperators

universe u

/-- **Every route-`8` core is empty or determined at G.** -/
theorem route8CoreEmpty (data : Parameters) (object : FiniteObject.{u}) :
    Route8CoreEmptyStatement data object := by
  letI : DecidableEq object.Vertex := Graph.Route8.vertexDecEq object
  intro index
  by_cases determined : ((Route8Census.presented object data.threshold data.LengthOK
      index).toEntry (HasCycleWithLength data.LengthOK)).Determined
  · exact Or.inr determined
  · exact Or.inl (Finset.card_eq_zero.mp
      (Route8.Entry.alpha_eq_zero_of_not_determined _ determined))

open Classical in
/-- The indexed entries of the route-`8` collection number `N_basin`. -/
theorem entriesOfComponents_card_eq_basin (data : Parameters) (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree)
    (scalePos : 0 < data.dischargeScale) :
    letI : DecidableEq object.Vertex := object.vertices.decEq
    let packing := canonicalWindowPacking data object
    let support := object.remainderSupport packing
    let routeEight := (object.canonicalPieces support).filter
      (Route8Survives data object packing)
    (Graph.Route8Census.entriesOfComponents object packing routeEight data.threshold
      data.dischargeScale).card =
      ∑ component ∈ routeEight,
        ∑ receiver ∈ Graph.VisibleEntry.saturatedReceivers object
            (object.pieceSupport support component) data.threshold data.dischargeScale,
          (Graph.VisibleEntry.silentExcess object
            (object.pieceSupport support component) data.threshold
            data.dischargeScale receiver).card := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  intro packing support routeEight
  have canonical : routeEight ⊆ object.canonicalPieces support := by
    intro component componentMem
    exact (Finset.mem_filter.mp componentMem).1
  have entryCount :
      (Graph.Route8Census.entriesOfComponents object
        packing routeEight data.threshold data.dischargeScale).card =
        ∑ component ∈ routeEight,
          ∑ receiver ∈ Graph.VisibleEntry.saturatedReceivers object
              (object.pieceSupport support component)
              data.threshold data.dischargeScale,
            (Graph.VisibleEntry.excessBasin object
              (object.pieceSupport support component)
              data.threshold data.dischargeScale receiver).card := by
    unfold Graph.Route8Census.entriesOfComponents
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun component _ => ?_
      rw [Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun receiver _ => ?_
        rw [Finset.card_image_of_injective]
        intro left right equal
        simpa using equal
      · intro left _ right _ different
        rw [Function.onFun, Finset.disjoint_left]
        intro index leftMem rightMem
        rw [Finset.mem_image] at leftMem rightMem
        obtain ⟨_, _, rfl⟩ := leftMem
        obtain ⟨_, _, equal⟩ := rightMem
        exact different (Eq.symm (by
          simpa using (congrArg (fun entry => entry.2.1) equal)))
    · intro left leftMem right _rightMem different
      rw [Function.onFun, Finset.disjoint_left]
      intro index leftIndex rightIndex
      rw [Finset.mem_biUnion] at leftIndex rightIndex
      obtain ⟨_, _, leftIndex⟩ := leftIndex
      obtain ⟨_, _, rightIndex⟩ := rightIndex
      rw [Finset.mem_image] at leftIndex rightIndex
      obtain ⟨_, _, rfl⟩ := leftIndex
      obtain ⟨_, _, equal⟩ := rightIndex
      have pieceEq :
          object.pieceSupport support left =
            object.pieceSupport support right := by
        simpa using (congrArg (fun entry => entry.1) equal).symm
      have disjoint :=
        Graph.SupportComponents.Connected.disjoint_members object support different
      obtain ⟨vertex, vertexMem⟩ :=
        Graph.SupportComponents.Connected.member_nonempty object support
          ((object.mem_canonicalPieces support).mp (canonical leftMem))
      have rightMem' : vertex ∈ object.pieceSupport support right :=
        pieceEq ▸ vertexMem
      exact Finset.disjoint_left.mp disjoint vertexMem rightMem'
  rw [entryCount]
  refine Finset.sum_congr rfl fun component componentMem => ?_
  refine Finset.sum_congr rfl fun receiver receiverMem => ?_
  have survives := (Finset.mem_filter.mp componentMem).2
  have isReceiver := FiniteObject.mem_receivers.mp
    (Finset.mem_filter.mp receiverMem).1
  rw [Graph.VisibleEntry.silentExcess_eq_excessBasin object _ data.threshold
    data.dischargeScale
    (degree_eq_threshold_of_ambientSurplus_eq_zero data object baseline
      survives.2.1 receiver isReceiver.1)
    isReceiver scalePos
    (fun saturated => survives.2.2.1 receiver isReceiver saturated)]

/-- **The strong rate, or the thin remainder.** -/
theorem route8StrongRate (data : Parameters) (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree)
    (scalePos : 0 < data.dischargeScale)
    (burden : Route8BasinBurden data object) :
    Route8StrongRateStatement data object := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have count := entriesOfComponents_card_eq_basin data object baseline scalePos
  obtain ⟨basinCount, hcount, scaled, hscaled, hle⟩ := burden
  unfold Route8StrongRateStatement
  dsimp only
  by_cases strong : data.dischargeScale * object.boundaryIncidence
        (object.remainderSupport (canonicalWindowPacking data object)) +
      data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount <
      (object.remainderSupport (canonicalWindowPacking data object)).card
  · left
    refine ⟨strong, fun lbd => ?_⟩
    have lbd' : (object.remainderSupport (canonicalWindowPacking data object)).card ≤
        scaled + data.dischargeScale * object.boundaryIncidence
          (object.remainderSupport (canonicalWindowPacking data object)) +
        data.bridgeMassFactor * data.dischargeScale *
          data.surplusThreshold object.vertexCount := by
      rw [hscaled]; exact lbd
    have basinPos : 0 < basinCount := by omega
    have cardPos : 0 < (Graph.Route8Census.entriesOfComponents object
        (canonicalWindowPacking data object)
        ((object.canonicalPieces
          (object.remainderSupport (canonicalWindowPacking data object))).filter
          (Route8Survives data object (canonicalWindowPacking data object)))
        data.threshold data.dischargeScale).card := by
      rw [count, ← hcount]; exact basinPos
    exact cardPos
  · right
    exact Nat.le_of_not_lt strong

/-- **The thin remainder isolates the windows.** -/
theorem route8ThinIsolation (data : Parameters) (object : FiniteObject.{u})
    (netcap : NetDeficiencyCapStatement data object)
    (join : Route8RateFailsJoinStatement data object) :
    Route8ThinIsolationStatement data object := by
  intro large thin
  have nc := netcap large
  have joinEq := join.1
  change _ + (2 * (data.windowOrder - 1) * _ + _) = _ at joinEq
  apply Nat.lt_of_mul_lt_mul_left (a := data.dischargeScale)
  have h2 : data.dischargeScale * (data.bridgeMassFactor * data.surplusThreshold
      object.vertexCount) = data.bridgeMassFactor * data.dischargeScale *
      data.surplusThreshold object.vertexCount := by ring
  have h1 := congrArg (fun z => data.dischargeScale * z) joinEq
  simp only [Nat.mul_add] at h1 nc ⊢
  have hT : data.spineScale * Core.ceilSqrt object.vertexCount =
      data.surplusThreshold object.vertexCount := rfl
  rw [hT] at nc
  omega

/-- **The exact stub count of each window and its distribution.** -/
theorem route8WindowStub (data : Parameters) (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree) :
    Route8WindowStubStatement data object := by
  have baselineAll : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
    degree_ge_of_minDegree data object baseline
  have valid := (canonicalWindowPacking_spec data object).1
  unfold Route8WindowStubStatement
  dsimp only
  have split : ∀ window ∈ canonicalWindowPacking data object, ∀ vertex,
      object.internalDegree window vertex +
          object.internalDegree
            (object.windowSupportOutside (canonicalWindowPacking data object) window)
            vertex +
          object.internalDegree
            (object.remainderSupport (canonicalWindowPacking data object)) vertex =
        object.degree vertex := by
    intro window present vertex
    have one := object.internalDegree_add_internalDegree_windowSupportOutside present vertex
    have two := object.internalDegree_add_internalDegree_compl
      (FiniteObject.windowSupport (canonicalWindowPacking data object)) vertex
    change _ + object.internalDegree
      (object.remainderSupport (canonicalWindowPacking data object)) vertex = _ at two
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro window present
    have sumDeg := object.sum_degree_eq_threshold_mul_card_add_ambientSurplus window
      data.threshold baselineAll
    have card : window.card = data.windowOrder := (valid.1 window present).2
    have mass := object.sum_internalDegree_window (valid.1 window present)
    have pointwise : (∑ vertex ∈ window, object.degree vertex) =
        (∑ vertex ∈ window, object.internalDegree window vertex) +
          (∑ vertex ∈ window, object.internalDegree
            (object.windowSupportOutside (canonicalWindowPacking data object) window)
            vertex) +
          (∑ vertex ∈ window, object.internalDegree
            (object.remainderSupport (canonicalWindowPacking data object)) vertex) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact (Finset.sum_congr rfl fun vertex _ => (split window present vertex).symm)
    rw [card] at sumDeg
    omega
  · rw [object.card_crossWindowIncidences valid]
  · classical
    letI : FinEnum object.Vertex := object.vertices
    have pairwise : ((canonicalWindowPacking data object : Finset (Finset object.Vertex)) :
        Set (Finset object.Vertex)).PairwiseDisjoint id := by
      intro left leftMember right rightMember distinct
      exact valid.2 left leftMember right rightMember distinct
    have collect : ∀ f : object.Vertex → Nat,
        ∑ window ∈ canonicalWindowPacking data object, ∑ vertex ∈ window, f vertex =
          ∑ vertex ∈ FiniteObject.windowSupport (canonicalWindowPacking data object),
            f vertex := by
      intro f
      rw [FiniteObject.windowSupport, Finset.sum_biUnion pairwise]
      simp only [id_eq]
    rw [collect, object.boundaryIncidence_remainderSupport_eq, FiniteObject.boundaryIncidence]
    refine Finset.sum_congr rfl fun vertex _ => ?_
    have two := object.internalDegree_add_internalDegree_compl
      (FiniteObject.windowSupport (canonicalWindowPacking data object)) vertex
    change _ + object.internalDegree
      (object.remainderSupport (canonicalWindowPacking data object)) vertex = _ at two
    omega

  · classical
    unfold FiniteObject.boundaryIncidence FiniteObject.ambientSurplus
    calc ∑ vertex ∈ object.remainderSupport (canonicalWindowPacking data object),
          (object.degree vertex - object.internalDegree
            (object.remainderSupport (canonicalWindowPacking data object)) vertex)
        ≤ ∑ vertex ∈ object.remainderSupport (canonicalWindowPacking data object),
          ((if object.internalDegree
              (object.remainderSupport (canonicalWindowPacking data object)) vertex <
                object.degree vertex then data.threshold else 0) +
            (object.degree vertex - data.threshold)) := by
          refine Finset.sum_le_sum fun vertex _ => ?_
          have := object.internalDegree_le_degree
            (object.remainderSupport (canonicalWindowPacking data object)) vertex
          have := baselineAll vertex
          split_ifs <;> omega
      _ = data.threshold * ((object.remainderSupport (canonicalWindowPacking data object)).filter
            fun vertex => object.internalDegree
              (object.remainderSupport (canonicalWindowPacking data object)) vertex <
                object.degree vertex).card +
          ∑ vertex ∈ object.remainderSupport (canonicalWindowPacking data object),
            (object.degree vertex - data.threshold) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
            smul_eq_mul, smul_zero, Nat.add_zero, Nat.mul_comm]

theorem thin_arith {δ s k β F p T n R e σ : Nat}
    (size : R + k * p = n) (thin : R ≤ s * e + F * s * T)
    (he : e ≤ β * p + σ) (hσ : σ ≤ T) :
    δ * n ≤ δ * (k + s * β) * p + δ * s * (1 + F) * T := by
  have h1 : s * e ≤ s * (β * p + T) :=
    Nat.mul_le_mul_left s (le_trans he (Nat.add_le_add_left hσ _))
  have h2 : R ≤ s * (β * p + T) + F * s * T := le_trans thin (Nat.add_le_add_right h1 _)
  calc δ * n = δ * (R + k * p) := by rw [size]
    _ ≤ δ * ((s * (β * p + T) + F * s * T) + k * p) :=
        Nat.mul_le_mul_left δ (Nat.add_le_add_right h2 _)
    _ = δ * (k + s * β) * p + δ * s * (1 + F) * T := by ring

/-- **The thin remainder forces a small order.** -/
theorem route8ThinSmall (data : Parameters) (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree)
    (threeLe : 3 ≤ data.threshold)
    (scaleCount : data.separatedScaleCount object.vertexCount =
      Nat.log2 object.vertexCount)
    (ceiling : SurplusAtOrBelowStatement data object)
    (densityCap : DensityCapStatement data object)
    (join : Route8RateFailsJoinStatement data object) :
    Route8ThinSmallStatement data object := by
  intro thin large
  have baselineAll : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
    degree_ge_of_minDegree data object baseline
  have valid := (canonicalWindowPacking_spec data object).1
  have windowSurplus :
      object.ambientSurplus (Graph.FiniteObject.windowSupport
          (canonicalWindowPacking data object)) data.threshold ≤
        data.surplusThreshold object.vertexCount :=
    le_trans (object.ambientSurplus_le_degreeSurplus _ data.threshold baselineAll)
      ceiling
  have remainder := object.remainderSupport_card_add_eq valid
  have joinEq := join.1
  have prod : coldExternalStubCount data * (canonicalWindowPacking data object).card =
      data.threshold * (data.windowOrder * (canonicalWindowPacking data object).card) -
        2 * (data.windowOrder - 1) * (canonicalWindowPacking data object).card := by
    simp only [coldExternalStubCount]
    rw [Nat.sub_mul, Nat.mul_assoc]
  have he : object.boundaryIncidence
        (object.remainderSupport (canonicalWindowPacking data object)) ≤
      coldExternalStubCount data * (canonicalWindowPacking data object).card +
        object.ambientSurplus (Graph.FiniteObject.windowSupport
          (canonicalWindowPacking data object)) data.threshold := by
    rw [prod]
    have debit : 2 * (data.windowOrder - 1) ≤ data.threshold * data.windowOrder := by
      have := Nat.mul_le_mul_right data.windowOrder threeLe
      omega
    have debit' : 2 * (data.windowOrder - 1) * (canonicalWindowPacking data object).card ≤
        data.threshold * (data.windowOrder * (canonicalWindowPacking data object).card) := by
      have := Nat.mul_le_mul_right (canonicalWindowPacking data object).card debit
      rw [Nat.mul_assoc data.threshold] at this
      exact this
    change _ + (2 * (data.windowOrder - 1) * _ + _) = _ at joinEq
    omega
  have lower := thin_arith (δ := data.threshold) remainder thin he windowSurplus
  have cardinality := (canonicalWindowPacking_spec data object).2.1
  have cap0 := densityCap
  unfold DensityCapStatement at cap0
  rw [← cardinality, scaleCount] at cap0
  simp only [Graph.dyadicScaleCount] at cap0
  have cap : 2 * (data.windowRate * Nat.log2 object.vertexCount *
      (canonicalWindowPacking data object).card) ≤
      (Nat.log2 object.vertexCount + 1) *
        (data.threshold * object.vertexCount + data.surplusThreshold object.vertexCount) +
      boundedDensityOrderSlack data * Nat.log2 object.vertexCount *
        data.surplusThreshold object.vertexCount := by
    have e : boundedDensityOrderSlack data * Nat.log2 object.vertexCount *
        data.surplusThreshold object.vertexCount =
        data.densitySlack * (data.windowRate * Nat.log2 object.vertexCount) *
          data.surplusThreshold object.vertexCount := by
      unfold boundedDensityOrderSlack; ring
    rw [e]; exact cap0
  have bound := Graph.densityOrderBound_of_lower_cap
    (A := thinPackingCoeff data) (D := thinSurplusCoeff data)
    (r := data.windowRate) (S := boundedDensityOrderSlack data)
    (δ := data.threshold) (size := object.vertexCount)
    (packing := (canonicalWindowPacking data object).card)
    (L := Nat.log2 object.vertexCount) (T := data.surplusThreshold object.vertexCount)
    (by unfold thinPackingCoeff thinSurplusCoeff; exact lower) cap
  exact Graph.densityOrderBound_false_of_large bound large

end Hypostructure.Graph.Contracts.RouteEight
