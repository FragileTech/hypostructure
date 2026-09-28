import Hypostructure.Graph.Statements.HubLinks
import Hypostructure.Graph.Contracts.Spine.JointHubs

/-!
# Contracts: links between the hubs of `R`, the slot relation, and the free side of G

Proof-agnostic contract lemmas for `Statements/HubLinks.lean`.  Each hypothesis is a ledger
fact (or its projection): the selection's avoidance and minimality, the presentation laws
(`δ = 3`, the dyadic length law, the label census), the baseline, `[8]`, `[10]`,
`K .surplusAbove`, and G's canonical capacity facts (`K .canonicalCapacityExplicit`,
`K .canonicalLedgerDeficit`, `K .canonicalFreeExcessOfCapped`).  One contract per
statement: `<statement>_holds`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine.HubLinks

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph.CapacityFreeSide
open Hypostructure.Graph.SameTokenBlockerRoles
open Hypostructure.Graph.Contracts.Spine.JointHubs

universe u v

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-! ## At `P₀` -/

theorem hubLinkStructure_holds (three : data.threshold = 3)
    (census : (Graph.WindowCurvature.sizeDistribution data.windowOrder).take 7 =
      [13, 60, 122, 122, 63, 17, 2])
    (baseline : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object) :
    HubLinkStructureStatement data object :=
  Graph.HubLinkObject.hubLinkStructure (maximal_of (order_of census)) (base_of three baseline)
    (slack_of three slack)

theorem hubClassCounts_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (slack : SlackIndependentStatement data object) :
    HubClassCountsStatement object :=
  Graph.HubLinkObject.hubClassCounts (base_of three baseline) (noProper_of three noProper)
    (slack_of three slack) (dyadic_of avoid lengthLaw)

theorem slotRelation_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (slack : SlackIndependentStatement data object) :
    SlotRelationStatement object :=
  Graph.HubLinkObject.slotRelation (base_of three baseline) (noProper_of three noProper)
    (slack_of three slack) (dyadic_of avoid lengthLaw)

theorem closedClasses_holds (three : data.threshold = 3)
    (census : (Graph.WindowCurvature.sizeDistribution data.windowOrder).take 7 =
      [13, 60, 122, 122, 63, 17, 2])
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (slack : SlackIndependentStatement data object) :
    ClosedClassesStatement data object :=
  Graph.HubLinkObject.closedClasses (base_of three baseline) (noProper_of three noProper)
    (slack_of three slack) (valid_of (order_of census))

theorem hubTwoHopLinks_holds (three : data.threshold = 3)
    (census : (Graph.WindowCurvature.sizeDistribution data.windowOrder).take 7 =
      [13, 60, 122, 122, 63, 17, 2])
    (baseline : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object) :
    HubTwoHopLinksStatement data object :=
  Graph.HubLinkObject.hubTwoHopLinks (maximal_of (order_of census)) (base_of three baseline)
    (slack_of three slack)

theorem slotLinear_holds (three : data.threshold = 3)
    (census : (Graph.WindowCurvature.sizeDistribution data.windowOrder).take 7 =
      [13, 60, 122, 122, 63, 17, 2])
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (slack : SlackIndependentStatement data object) :
    SlotLinearStatement data object :=
  Graph.HubLinkObject.slotLinear (maximal_of (order_of census)) (base_of three baseline)
    (noProper_of three noProper) (slack_of three slack) (dyadic_of avoid lengthLaw)
    (valid_of (order_of census))

/-! ## The strict arm -/

theorem scalePressure_holds (three : data.threshold = 3)
    (census : (Graph.WindowCurvature.sizeDistribution data.windowOrder).take 7 =
      [13, 60, 122, 122, 63, 17, 2])
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (slack : SlackIndependentStatement data object)
    (above : SurplusAboveStatement data object) :
    ScalePressureStatement data object := by
  have base := base_of three baseline
  refine Graph.HubLinkObject.scalePressure (maximal_of (order_of census)) base
    (noProper_of three noProper) (slack_of three slack) (dyadic_of avoid lengthLaw)
    (valid_of (order_of census)) _ _ ?_
  have h := above
  unfold SurplusAboveStatement Parameters.surplusThreshold at h
  rw [three, ← Graph.JointObject.sigma_eq base, Graph.JointObject.vertexCount_eq] at h
  exact h

/-! ## The free side of G's canonical capacity charge -/

theorem freeSideStructure_holds
    {BranchState : Graph.FiniteObject.{u} → Type v} {Presentation : Type}
    {presentation : Presentation}
    (minimalSel : SelectionMinimality BranchState Presentation presentation data object)
    (baseline : MinDegreeBaselineStatement data object)
    (explicit : CanonicalCapacityExplicitStatement data object) :
    FreeSideStructureStatement data object := by
  obtain ⟨active, avoids, conn, hc⟩ := explicit
  refine ⟨active, _, hc, rfl, fun pair free => ?_⟩
  have minimal : ∀ smaller : Graph.FiniteObject.{u}, smaller.LexicographicallySmaller object →
      data.threshold ≤ smaller.minDegree → Graph.HasCycleWithLength data.LengthOK smaller :=
    fun H hlt hb => minimalSel.sizeMinimal H hlt hb
  obtain ⟨p, q, hp, hq, hpq, hpair, dD, dT, dR, cen, e1, e2, noE, noF⟩ :=
    free_structure active (explicitCapacity active avoids conn) rfl free
  obtain ⟨p', q', hp', hq', hne', hpair', alt⟩ :=
    free_triangular_or_centreShoulder active (explicitCapacity active avoids conn) rfl
      baseline minimal free
  have hpp : (p' = p ∧ q' = q) ∨ (p' = q ∧ q' = p) := by
    have h1 := (hpair p').1 ((hpair' p').2 (Or.inl rfl))
    have h2 := (hpair q').1 ((hpair' q').2 (Or.inr rfl))
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · exact (hne' rfl).elim
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact (hne' rfl).elim
  refine ⟨p, q, hp, hq, hpq, hpair, dD, dT, dR, cen, e1, e2, noE, noF, ?_⟩
  rcases hpp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact alt
  · rcases alt with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))

theorem freeSideCount_holds (three : data.threshold = 3)
    (structure_ : FreeSideStructureStatement data object)
    (deficit : CanonicalLedgerDeficitStatement data object)
    (capped : CanonicalFreeExcessOfCappedStatement data object) :
    FreeSideCountStatement data object := by
  classical
  obtain ⟨active, c, hc, hact, red⟩ := structure_
  letI := object.vertexPairDecidableEq
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have hcount : freeCount data object c ≤
      tauAt (threshold := data.threshold) (Graph.pairResponseChordEnds active) *
          object.degreeSurplus data.threshold +
        ∑ q ∈ object.excessPorts data.threshold,
          ∑ v ∈ (Graph.pairResponseActivation active).localBuffer q,
            sAt object data.threshold v := by
    have key := Graph.PairCount.card_pairs_le (object.excessPorts data.threshold) Prod.fst
      (Graph.pairResponseActivation active).localBuffer
      (fun p => object.graph.Adj (Graph.pairResponseChordEnds active p).1
        (Graph.pairResponseChordEnds active p).2)
      (Graph.freeSide object.vertexPairDecidableEq (object.portPairSchedule data.threshold)
        c.tokenOrder c.Eligible c.eligibleDecidable) ?_
    · rw [active.count] at key
      unfold freeCount tauAt sAt
      convert key using 7
    · intro pair hpair
      obtain ⟨p, q, hp, hq, hpq, hmem, -, -, -, -, -, -, -, -, alt⟩ := red pair hpair
      refine ⟨p, hp, q, hq, hpq, ?_, ?_⟩
      · ext x; rw [hmem]; simp
      · rw [Graph.pairResponseActivation_localBuffer_of_mem active hp,
          Graph.pairResponseActivation_localBuffer_of_mem active hq]
        exact alt
  obtain ⟨c', L, hc', hL, hg2⟩ := deficit
  obtain ⟨c'', L', hc'', hL', hcap⟩ := capped
  obtain rfl : c' = c := Option.some_injective _ (hc'.symm.trans hc)
  obtain rfl : c'' = c' := Option.some_injective _ (hc''.symm.trans hc)
  obtain rfl : L' = L := Option.some_injective _ (hL'.symm.trans hL)
  have hz : (freeCount data object c'' : ℤ) ≤ ((tauAt (threshold := data.threshold)
      (Graph.pairResponseChordEnds active) * object.degreeSurplus data.threshold +
      ∑ q ∈ object.excessPorts data.threshold,
        ∑ v ∈ (Graph.pairResponseActivation active).localBuffer q,
          sAt object data.threshold v : ℕ) : ℤ) := Nat.cast_le.2 hcount
  refine ⟨active, c'', L', hc, hL, hact, active.count,
    fun v => card_ports_centred object _ v, hcount, by linarith,
    fun cap => by have := hcap cap; linarith, fun Δ hΔ => ?_⟩
  set σ := object.degreeSurplus data.threshold
  have hΛ : ∑ q ∈ object.excessPorts data.threshold,
      ∑ v ∈ (Graph.pairResponseActivation active).localBuffer q, sAt object data.threshold v ≤
      σ * (3 * (Δ - 3)) := by
    calc ∑ q ∈ object.excessPorts data.threshold,
          ∑ v ∈ (Graph.pairResponseActivation active).localBuffer q, sAt object data.threshold v
        ≤ ∑ q ∈ object.excessPorts data.threshold, 3 * (Δ - 3) := by
          refine Finset.sum_le_sum fun q _ => ?_
          calc ∑ v ∈ (Graph.pairResponseActivation active).localBuffer q,
                sAt object data.threshold v
              ≤ ∑ v ∈ (Graph.pairResponseActivation active).localBuffer q, (Δ - 3) := by
                refine Finset.sum_le_sum fun v _ => ?_
                rw [card_ports_centred, three]
                exact Nat.sub_le_sub_right (hΔ v) 3
            _ = ((Graph.pairResponseActivation active).localBuffer q).card * (Δ - 3) := by
                rw [Finset.sum_const, smul_eq_mul]
            _ ≤ 3 * (Δ - 3) := Nat.mul_le_mul_right _ (card_localBuffer_le active q)
      _ = σ * (3 * (Δ - 3)) := by
          rw [Finset.sum_const, smul_eq_mul, active.count]
  have hsum : tauAt (threshold := data.threshold) (Graph.pairResponseChordEnds active) * σ +
      ∑ q ∈ object.excessPorts data.threshold,
        ∑ v ∈ (Graph.pairResponseActivation active).localBuffer q, sAt object data.threshold v ≤
      σ * (tauAt (threshold := data.threshold) (Graph.pairResponseChordEnds active) +
        3 * (Δ - 3)) := by
    rw [Nat.mul_add, Nat.mul_comm σ]; omega
  refine ⟨le_trans hcount hsum, fun cap hK => ?_⟩
  have h := hcap cap
  have hz2 := Nat.cast_le (α := ℤ) |>.2 hsum
  have sup : c''.tokens.card ≤ 8 * object.vertexCount + σ := by
    have := L'.supply
    simp only [Graph.FiniteObject.capacityTokenSupply,
      Graph.FiniteObject.primitiveCarrierSupply] at this
    have e3 : 3 * (data.threshold - 1) * object.vertexCount = 6 * object.vertexCount := by
      rw [three]
    have this' : c''.tokens.card ≤
        3 * (data.threshold - 1) * object.vertexCount + 2 * object.vertexCount + σ := this
    omega
  have supZ : (c''.tokens.card : ℤ) ≤ ((8 * object.vertexCount + σ : ℕ) : ℤ) := Nat.cast_le.2 sup
  have hn : (object.vertexCount : ℤ) ≤ (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 := by
    exact_mod_cast Core.le_ceilSqrt_sq object.vertexCount
  have hB : (0 : ℤ) ≤ (certificationBudget data object : ℤ) := Nat.cast_nonneg _
  have hM : (0 : ℤ) ≤ (homogeneousTokenCap data.routingLabelBound : ℤ) := Nat.cast_nonneg _
  have p2 : (0 : ℤ) ≤ 2 * (homogeneousTokenCap data.routingLabelBound : ℤ) *
      (((8 * object.vertexCount + σ : ℕ) : ℤ) - (c''.tokens.card : ℤ)) :=
    mul_nonneg (mul_nonneg (by norm_num) hM) (by linarith)
  have hKn := mul_le_mul_of_nonneg_right hn hK
  nlinarith

/-! ## The free side against the hubs, and the extended charge -/

theorem freeSideHubs_holds (three : data.threshold = 3) (hL4 : data.LengthOK 4)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (slack : SlackIndependentStatement data object)
    (count : FreeSideCountStatement data object) :
    FreeSideHubsStatement data object := by
  classical
  obtain ⟨active, c, L, hc, hL, -, hcard, -, hcount, -, hcap, -⟩ := count
  letI : FinEnum object.Vertex := object.vertices
  set σ := object.degreeSurplus data.threshold
  set hH := sparseHighDegreeCount data object
  have hΛ : ∑ q ∈ object.excessPorts data.threshold,
      ∑ v ∈ (Graph.pairResponseActivation active).localBuffer q, sAt object data.threshold v ≤
      σ * (hH - 1) := by
    have e := Lambda_eq (object.excessPorts data.threshold) Prod.fst
      (Graph.pairResponseActivation active).localBuffer
    have e' : ∑ q ∈ object.excessPorts data.threshold,
        ∑ v ∈ (Graph.pairResponseActivation active).localBuffer q, sAt object data.threshold v =
        ∑ p ∈ object.excessPorts data.threshold, ((object.excessPorts data.threshold).filter
          fun q => p.1 ∈ (Graph.pairResponseActivation active).localBuffer q).card := by
      unfold sAt; convert e using 4 with q _ v _; ext x; simp
    rw [e']
    calc ∑ p ∈ object.excessPorts data.threshold, ((object.excessPorts data.threshold).filter
          fun q => p.1 ∈ (Graph.pairResponseActivation active).localBuffer q).card
        ≤ ∑ _p ∈ object.excessPorts data.threshold, (hH - 1) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hi := Graph.FiniteObject.centre_high_of_mem_excessPorts hp
          have mem : p.1 ∈ (Finset.univ.filter fun w => object.degree w ≠ data.threshold) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
          refine (centreIncidence_le active hL4 avoid slack p.1 hi).trans ?_
          rw [Finset.card_erase_of_mem mem]
      _ = σ * (hH - 1) := by rw [Finset.sum_const, smul_eq_mul, hcard]
  have hsum : tauAt (threshold := data.threshold) (Graph.pairResponseChordEnds active) * σ +
      ∑ q ∈ object.excessPorts data.threshold,
        ∑ v ∈ (Graph.pairResponseActivation active).localBuffer q, sAt object data.threshold v ≤
      σ * (tauAt (threshold := data.threshold) (Graph.pairResponseChordEnds active) + (hH - 1)) := by
    rw [Nat.mul_add, Nat.mul_comm σ]; omega
  refine ⟨active, c, L, hc, hL, le_trans hcount hsum, fun cap hK => ?_⟩
  have h := hcap cap
  have sup : c.tokens.card ≤ 8 * object.vertexCount + σ := by
    have := L.supply
    simp only [Graph.FiniteObject.capacityTokenSupply,
      Graph.FiniteObject.primitiveCarrierSupply] at this
    have e3 : 3 * (data.threshold - 1) * object.vertexCount = 6 * object.vertexCount := by
      rw [three]
    have this' : c.tokens.card ≤
        3 * (data.threshold - 1) * object.vertexCount + 2 * object.vertexCount + σ := this
    omega
  have supZ : (c.tokens.card : ℤ) ≤ ((8 * object.vertexCount + σ : ℕ) : ℤ) := Nat.cast_le.2 sup
  have hn : (object.vertexCount : ℤ) ≤ (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 := by
    exact_mod_cast Core.le_ceilSqrt_sq object.vertexCount
  have hB : (0 : ℤ) ≤ (certificationBudget data object : ℤ) := Nat.cast_nonneg _
  have hM : (0 : ℤ) ≤ (homogeneousTokenCap data.routingLabelBound : ℤ) := Nat.cast_nonneg _
  have p2 : (0 : ℤ) ≤ 2 * (homogeneousTokenCap data.routingLabelBound : ℤ) *
      (((8 * object.vertexCount + σ : ℕ) : ℤ) - (c.tokens.card : ℤ)) :=
    mul_nonneg (mul_nonneg (by norm_num) hM) (by linarith)
  have hKn := mul_le_mul_of_nonneg_right hn hK
  have hz := Nat.cast_le (α := ℤ) |>.2 hsum
  nlinarith

/-- The extended charge at G's canonical capacity presentation, all conjuncts. -/
theorem extended_core
    {BranchState : Graph.FiniteObject.{u} → Type v} {Presentation : Type}
    {presentation : Presentation} (three : data.threshold = 3) (hL4 : data.LengthOK 4)
    (minimalSel : SelectionMinimality BranchState Presentation presentation data object)
    (baseline : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object)
    (explicit : CanonicalCapacityExplicitStatement data object)
    (pcd : PairCountDeficitStatement data object)
    (partition : CanonicalBlockedFreePartitionStatement data object)
    (ceil : CeilSqrtAboveScaleStatement data object) :
    ∃ c : SurplusCapacity data object, canonicalCapacity data object = some c ∧
      extFree data.LengthOK c = ∅ ∧
      (object.degreeSurplus data.threshold).choose 2 =
        ∑ t ∈ c.tokens, extLoad data.LengthOK c t ∧
      c.tokens.card ≤ 8 * object.vertexCount + object.degreeSurplus data.threshold ∧
      (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 * pairDeficitCoefficient data +
          2 * (homogeneousTokenCap data.routingLabelBound : ℤ) *
            ((8 * object.vertexCount + object.degreeSurplus data.threshold : ℕ) -
              (c.tokens.card : ℤ)) +
          2 * (certificationBudget data object : ℤ) ≤
        2 * ∑ t ∈ c.tokens,
          ((extLoad data.LengthOK c t : ℤ) - homogeneousTokenCap data.routingLabelBound) ∧
      (0 < pairDeficitCoefficient data →
        ∃ t ∈ c.tokens, homogeneousTokenCap data.routingLabelBound < extLoad data.LengthOK c t) ∧
      (∀ p ∈ object.excessPorts data.threshold,
        newLoad data.LengthOK c p ≤ (sparseHighDegreeCount data object - 1) +
          (by classical exact if TriPortAt object p then object.degreeSurplus data.threshold
            else 0)) := by
  obtain ⟨active, avoids, conn, hc⟩ := explicit
  set σ := object.degreeSurplus data.threshold
  set n := object.vertexCount
  set M₀ := homogeneousTokenCap data.routingLabelBound
  have minimal : ∀ smaller : Graph.FiniteObject.{u}, smaller.LexicographicallySmaller object →
      data.threshold ≤ smaller.minDegree → Graph.HasCycleWithLength data.LengthOK smaller :=
    fun H hlt hb => minimalSel.sizeMinimal H hlt hb
  set c := explicitCapacity active avoids conn
  have cover : ∀ pair ∈ object.portPairSchedule data.threshold,
      (c.activation.blockers pair).Nonempty ∨
        CentreShoulderBlocks data.LengthOK object pair ∨ TriangularBlocks object pair :=
    fun pair sched => extended_coverage active c rfl baseline minimal slack hL4 avoids sched
  have free0 := extFree_eq_empty data.LengthOK c cover
  have part := extPartition data.LengthOK c
  rw [free0, Finset.card_empty, add_zero] at part
  have schedCard : (object.portPairSchedule data.threshold).card = σ.choose 2 := by
    letI := object.vertexPairDecidableEq
    unfold Graph.FiniteObject.portPairSchedule
    rw [Graph.CanonicalFibreLedger.card_pairs, active.count]
  rw [schedCard] at part
  have sup : c.tokens.card ≤ 8 * n + σ := by
    obtain ⟨c', L, hc', -, -⟩ := partition
    obtain rfl : c' = c := Option.some_injective _ (hc'.symm.trans hc)
    have := L.supply
    simp only [Graph.FiniteObject.capacityTokenSupply,
      Graph.FiniteObject.primitiveCarrierSupply] at this
    have e3 : 3 * (data.threshold - 1) * n = 6 * n := by rw [three]
    have this' : c.tokens.card ≤ 3 * (data.threshold - 1) * n + 2 * n + σ := this
    omega
  have pcd' := pcd
  unfold PairCountDeficitStatement at pcd'
  have sumZ : ((σ.choose 2 : ℕ) : ℤ) = ∑ t ∈ c.tokens, (extLoad data.LengthOK c t : ℤ) := by
    rw [part]; push_cast; rfl
  have supZ : (c.tokens.card : ℤ) ≤ ((8 * n + σ : ℕ) : ℤ) := Nat.cast_le.2 sup
  have quant : (Core.ceilSqrt n : ℤ) ^ 2 * pairDeficitCoefficient data +
      2 * (M₀ : ℤ) * ((8 * n + σ : ℕ) - (c.tokens.card : ℤ)) +
      2 * (certificationBudget data object : ℤ) ≤
      2 * ∑ t ∈ c.tokens, ((extLoad data.LengthOK c t : ℤ) - M₀) := by
    rw [Finset.sum_sub_distrib, ← sumZ, Finset.sum_const, nsmul_eq_mul]
    linarith
  refine ⟨c, hc, free0, part, sup, quant, fun hKpos => ?_, fun p hp => ?_⟩
  · by_contra hno
    push Not at hno
    have le : ∑ t ∈ c.tokens, ((extLoad data.LengthOK c t : ℤ) - M₀) ≤ 0 :=
      Finset.sum_nonpos fun t ht => sub_nonpos.2 (by exact_mod_cast hno t ht)
    have cs1 : (0 : ℤ) < (Core.ceilSqrt n : ℤ) ^ 2 * pairDeficitCoefficient data := by
      have h := ceil
      unfold CeilSqrtAboveScaleStatement at h
      have : 1 ≤ Core.ceilSqrt n := le_trans (Nat.le_add_left 1 _) h
      have : (1 : ℤ) ≤ (Core.ceilSqrt n : ℤ) := by exact_mod_cast this
      positivity
    have hB : (0 : ℤ) ≤ (certificationBudget data object : ℤ) := Nat.cast_nonneg _
    have hM : (0 : ℤ) ≤ (M₀ : ℤ) := Nat.cast_nonneg _
    have p2 : (0 : ℤ) ≤ 2 * (M₀ : ℤ) * (((8 * n + σ : ℕ) : ℤ) - (c.tokens.card : ℤ)) :=
      mul_nonneg (mul_nonneg (by norm_num) hM) (by linarith)
    linarith
  · refine (newLoad_le data.LengthOK c p).trans (add_le_add ?_ ?_)
    · letI : FinEnum object.Vertex := object.vertices
      have hi := Graph.FiniteObject.centre_high_of_mem_excessPorts hp
      have mem : p.1 ∈ (Finset.univ.filter fun w => object.degree w ≠ data.threshold) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      have h1 := adjEndpoint_le (threshold := data.threshold) hL4 avoids p.1
      rw [Finset.card_erase_of_mem mem] at h1
      refine le_trans (le_of_eq ?_) (h1.trans (le_of_eq ?_))
      · congr 1; ext q; simp only [Finset.mem_filter]
      · unfold sparseHighDegreeCount; congr 2
    · by_cases hT : TriPortAt object p <;> simp [hT, active.count, σ]

theorem extFreeEmpty_holds
    {BranchState : Graph.FiniteObject.{u} → Type v} {Presentation : Type}
    {presentation : Presentation} (three : data.threshold = 3) (hL4 : data.LengthOK 4)
    (minimalSel : SelectionMinimality BranchState Presentation presentation data object)
    (baseline : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object)
    (explicit : CanonicalCapacityExplicitStatement data object)
    (pcd : PairCountDeficitStatement data object)
    (partition : CanonicalBlockedFreePartitionStatement data object)
    (ceil : CeilSqrtAboveScaleStatement data object) :
    ExtFreeEmptyStatement data object := by
  obtain ⟨c, hc, h, -⟩ := extended_core three hL4 minimalSel baseline slack explicit pcd
    partition ceil
  exact ⟨c, hc, h⟩

theorem extLoadSum_holds
    {BranchState : Graph.FiniteObject.{u} → Type v} {Presentation : Type}
    {presentation : Presentation} (three : data.threshold = 3) (hL4 : data.LengthOK 4)
    (minimalSel : SelectionMinimality BranchState Presentation presentation data object)
    (baseline : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object)
    (explicit : CanonicalCapacityExplicitStatement data object)
    (pcd : PairCountDeficitStatement data object)
    (partition : CanonicalBlockedFreePartitionStatement data object)
    (ceil : CeilSqrtAboveScaleStatement data object) :
    ExtLoadSumStatement data object := by
  obtain ⟨c, hc, -, h1, h2, -⟩ := extended_core three hL4 minimalSel baseline slack explicit pcd
    partition ceil
  exact ⟨c, hc, h1, h2⟩

theorem extOverload_holds
    {BranchState : Graph.FiniteObject.{u} → Type v} {Presentation : Type}
    {presentation : Presentation} (three : data.threshold = 3) (hL4 : data.LengthOK 4)
    (minimalSel : SelectionMinimality BranchState Presentation presentation data object)
    (baseline : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object)
    (explicit : CanonicalCapacityExplicitStatement data object)
    (pcd : PairCountDeficitStatement data object)
    (partition : CanonicalBlockedFreePartitionStatement data object)
    (ceil : CeilSqrtAboveScaleStatement data object) :
    ExtOverloadStatement data object := by
  obtain ⟨c, hc, -, -, -, h, -⟩ := extended_core three hL4 minimalSel baseline slack explicit pcd
    partition ceil
  exact ⟨c, hc, h⟩

theorem extOverloadedToken_holds
    {BranchState : Graph.FiniteObject.{u} → Type v} {Presentation : Type}
    {presentation : Presentation} (three : data.threshold = 3) (hL4 : data.LengthOK 4)
    (minimalSel : SelectionMinimality BranchState Presentation presentation data object)
    (baseline : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object)
    (explicit : CanonicalCapacityExplicitStatement data object)
    (pcd : PairCountDeficitStatement data object)
    (partition : CanonicalBlockedFreePartitionStatement data object)
    (ceil : CeilSqrtAboveScaleStatement data object) :
    ExtOverloadedTokenStatement data object := by
  obtain ⟨c, hc, -, -, -, -, h, -⟩ := extended_core three hL4 minimalSel baseline slack explicit
    pcd partition ceil
  exact ⟨c, hc, h⟩

theorem newLoadBound_holds
    {BranchState : Graph.FiniteObject.{u} → Type v} {Presentation : Type}
    {presentation : Presentation} (three : data.threshold = 3) (hL4 : data.LengthOK 4)
    (minimalSel : SelectionMinimality BranchState Presentation presentation data object)
    (baseline : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object)
    (explicit : CanonicalCapacityExplicitStatement data object)
    (pcd : PairCountDeficitStatement data object)
    (partition : CanonicalBlockedFreePartitionStatement data object)
    (ceil : CeilSqrtAboveScaleStatement data object) :
    NewLoadBoundStatement data object := by
  obtain ⟨c, hc, -, -, -, -, -, h⟩ := extended_core three hL4 minimalSel baseline slack explicit
    pcd partition ceil
  exact ⟨c, hc, h⟩

theorem separatedPairs_holds (explicit : CanonicalCapacityExplicitStatement data object) :
    SeparatedPairsStatement data object := by
  obtain ⟨active, avoids, conn, hc⟩ := explicit
  refine ⟨active, _, hc, rfl, fun p q pair hp hpair dD dR =>
    sep_blockers_kind active (explicitCapacity active avoids conn) rfl hp hpair dD dR, ?_⟩
  letI : FinEnum object.Vertex := object.vertices
  letI := object.vertexPairDecidableEq
  classical
  set P := object.excessPorts data.threshold
  set Dx := (Graph.pairResponseActivation active).declaredSupport
  set Rx := (Graph.pairResponseActivation active).returnSupport
  have sched : object.portPairSchedule data.threshold = P.powersetCard 2 := rfl
  have hσ : (object.degreeSurplus data.threshold).choose 2 = (P.powersetCard 2).card := by
    rw [Finset.card_powersetCard, active.count]
  have mD := Graph.PairCount.card_meeting_pairs_le P Dx Finset.univ
    (fun _ _ => Finset.subset_univ _)
  have mR := Graph.PairCount.card_meeting_pairs_le P Rx Finset.univ
    (fun _ _ => Finset.subset_univ _)
  show (object.degreeSurplus data.threshold).choose 2 ≤ _
  rw [hσ, sched]
  refine le_trans (Finset.card_le_card (s := P.powersetCard 2)
    (t := ((P.powersetCard 2).filter fun pr => ∃ p ∈ pr, ∃ q ∈ pr, p ≠ q ∧
        ¬ Disjoint (Dx p) (Dx q)) ∪
      ((P.powersetCard 2).filter fun pr => ∃ p ∈ pr, ∃ q ∈ pr, p ≠ q ∧
        ¬ Disjoint (Rx p) (Rx q)) ∪
      ((P.powersetCard 2).filter fun pr => ∀ p ∈ pr, ∀ q ∈ pr, p ≠ q →
        Disjoint (Dx p) (Dx q) ∧ Disjoint (Rx p) (Rx q))) ?_) ?_
  · intro pr hpr
    by_cases h1 : ∃ p ∈ pr, ∃ q ∈ pr, p ≠ q ∧ ¬ Disjoint (Dx p) (Dx q)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hpr, h1⟩))
    by_cases h2 : ∃ p ∈ pr, ∃ q ∈ pr, p ≠ q ∧ ¬ Disjoint (Rx p) (Rx q)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hpr, h2⟩))
    refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hpr, fun p hp q hq hpq => ⟨?_, ?_⟩⟩)
    · by_contra h; exact h1 ⟨p, hp, q, hq, hpq, h⟩
    · by_contra h; exact h2 ⟨p, hp, q, hq, hpq, h⟩
  · refine (Finset.card_union_le _ _).trans (add_le_add ((Finset.card_union_le _ _).trans
      (add_le_add ?_ ?_)) le_rfl)
    · convert mD using 3
    · convert mR using 3

end Hypostructure.Graph.Contracts.Spine.HubLinks
