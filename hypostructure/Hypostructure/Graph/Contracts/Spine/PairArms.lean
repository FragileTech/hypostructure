import Hypostructure.Graph.Statements.PairArms
import Hypostructure.Graph.Contracts.Spine.JointHubs

/-!
# Contracts: the two arms of G's pair-code configuration

Proof-agnostic contract lemmas for `Statements/PairArms.lean`.  Hypotheses are ledger facts:
the selection's avoidance, the presentation laws, the baseline, `[8]`, `[9]`, `[10]`, the
return avoidance, the replacement exclusion, `K .surplusAbove`, `K .highEndpointSwitch`,
and G's canonical capacity presentation.  Clause (b), stated about G, is empty at G
(lem:sparse-exit-b-empty), so no contract is stated at its pinned witness.  One contract per statement: `<statement>_holds`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine.PairArms

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.FiniteObject
open Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph.Strategy.InterfaceReplacement
open Hypostructure.Graph.CapacityFreeSide
open Hypostructure.Graph.PairArms
open Hypostructure.Graph.SameTokenBlockerRoles

universe u v

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

theorem portEndDegree_holds (baseline : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object) :
    PortEndDegreeStatement data object :=
  fun _ hd => port_end_degree hd slack (fun v => le_trans baseline (object.minDegree_le_degree v))

open Classical in
theorem pairArmAPattern_holds (explicit : CanonicalCapacityExplicitStatement data object) :
    PairArmAPatternStatement data object := by
  intro armA
  classical
  obtain ⟨active, avoids, conn, hc⟩ := explicit
  obtain ⟨overload, pattern, hov, -, spec⟩ := armA.2.2.1
  obtain ⟨⟨cap, cert⟩, token, role⟩ := overload
  have hcd : canonicalCertifiedCapacityData data object = some ⟨cap, cert⟩ := by
    unfold canonicalOverload at hov
    cases h : canonicalCertifiedCapacityData data object with
    | none => rw [h] at hov; simp at hov
    | some l =>
        rw [h] at hov
        simp only [Option.bind_some, Option.map_eq_some_iff] at hov
        obtain ⟨ch, -, hch⟩ := hov
        rw [(Sigma.mk.inj_iff.1 hch).1]
  have hcap := ((canonicalCertifiedCapacityData_eq_some_iff data object cap cert).1 hcd).1
  rw [hc] at hcap
  obtain rfl := Option.some.inj hcap
  have spec' : HomogeneousPatternSpec data object cert token role pattern := spec
  refine ⟨active, avoids, conn, hc, cert, token, role, pattern, hcd, hov, spec', ?_⟩
  clear armA hov hcd hcap spec
  obtain ⟨sub, ms, bound, -⟩ := spec'
  have hact : (explicitCapacity active avoids conn).activation = recordSparsePairDEBlockers
      (Baseline := Graph.MinimumDegreeAtLeast data.threshold) (LengthOK := data.LengthOK)
      (pairResponseActivation active) (object.portPairSchedule data.threshold) := rfl
  -- every pattern pair: schedule, charge, canonical blocker, role
  have per : ∀ π ∈ pattern, π ∈ object.portPairSchedule data.threshold ∧
      capacityCharge (explicitCapacity active avoids conn).activation
        (explicitCapacity active avoids conn).carrier data.threshold
        (explicitCapacity active avoids conn).packing π = some token ∧
      ∃ b, canonicalBlocker (explicitCapacity active avoids conn).activation π = some b ∧
        b.kind = role.blocker ∧ role.token = token.subtype := by
    intro π hπ
    obtain ⟨hs, hch, hr⟩ := mem_roleFibre_charge cert.ledger (sub hπ)
    obtain ⟨b, hb⟩ := canonical_of_charge _ _ _ _ hch
    refine ⟨hs, hch, b, hb, ?_, ?_⟩
    · rw [← hr]; unfold capacityRole; rw [hb]; rfl
    · rw [← hr]; unfold capacityRole; rw [hch]; rfl
  have hne : pattern.Nonempty := by
    have : 1 ≤ Graph.SameTokenRoutingGerms.patternBound (SurplusRoutingLabel data) := by
      unfold Graph.SameTokenRoutingGerms.patternBound; exact Nat.le_add_left 1 _
    exact Finset.card_pos.1 (lt_of_lt_of_le this bound)
  obtain ⟨π₀, hπ₀⟩ := hne
  have hsubtype : role.token = token.subtype := (per π₀ hπ₀).2.2.choose_spec.2.2
  have h2 : ∀ π ∈ pattern, π.card = 2 := fun π hπ =>
    cert.ledger.presented.pairs_roleFibre token role π (sub hπ)
  refine ⟨card_support_ge pattern h2 ⟨π₀, hπ₀⟩ ms, hsubtype,
    fun π hπ => ⟨(per π hπ).1, (per π hπ).2.1, (per π hπ).2.2.choose,
      (per π hπ).2.2.choose_spec.1, (per π hπ).2.2.choose_spec.2.1⟩, ?_⟩
  -- the classification of every pair
  have cls := fun π (hπ : π ∈ pattern) =>
    pair_classification active (explicitCapacity active avoids conn) hact avoids
      (per π hπ).1 (per π hπ).2.1 (per π hπ).2.2.choose_spec.1
  have kindOf := fun π (hπ : π ∈ pattern) => (per π hπ).2.2.choose_spec.2.1
  have canOf := fun π (hπ : π ∈ pattern) => (per π hπ).2.2.choose_spec.1
  rcases cls π₀ hπ₀ with ⟨w, hw, htw, -⟩ | ⟨w, hw, htw, -⟩ | ⟨c, hcw, htc⟩ | ⟨S, hS, hF⟩
  · -- (a)
    left
    have hk : role.blocker = .sharedDeclaredSupport := by
      rw [← kindOf π₀ hπ₀, hw]; rfl
    refine ⟨hk, w, htw, fun π hπ => ?_⟩
    rcases cls π hπ with ⟨w', hw', htw', hD⟩ | ⟨w', hw', -, -⟩ | ⟨c', hc', -⟩ | ⟨S', hS', -⟩
    · have hww : w' = w := by
        rcases htw with h1 | ⟨j, h1⟩ <;> rcases htw' with h2 | ⟨j', h2⟩ <;> rw [h1] at h2
        · simp only [CapacityToken.primitive.injEq, Sum.inl.injEq] at h2; exact h2.symm
        · cases h2
        · cases h2
        · simp only [CapacityToken.remainder.injEq, Prod.mk.injEq] at h2; exact h2.1.symm
      subst hww
      exact ⟨(canOf π hπ).trans (by rw [hw']), hD⟩
    · have e := kindOf π hπ
      rw [hw', hk] at e
      exact absurd e (by simp [Blocker.kind])
    · have e := kindOf π hπ
      rw [hc', hk] at e
      exact absurd e (by simp [Blocker.kind])
    · have e := kindOf π hπ
      rw [hS', hk] at e
      exact absurd e (by simp [Blocker.kind])
  · -- (b)
    right; left
    have hk : role.blocker = .sharedReturnSupport := by
      rw [← kindOf π₀ hπ₀, hw]; rfl
    refine ⟨hk, w, htw, fun π hπ => ?_⟩
    rcases cls π hπ with ⟨w', hw', -, -⟩ | ⟨w', hw', htw', hD⟩ | ⟨c', hc', -⟩ | ⟨S', hS', -⟩
    · have e := kindOf π hπ
      rw [hw', hk] at e
      exact absurd e (by simp [Blocker.kind])
    · have hww : w' = w := by
        rcases htw with h1 | ⟨j, h1⟩ <;> rcases htw' with h2 | ⟨j', h2⟩ <;> rw [h1] at h2
        · simp only [CapacityToken.primitive.injEq, Sum.inl.injEq] at h2; exact h2.symm
        · cases h2
        · cases h2
        · simp only [CapacityToken.remainder.injEq, Prod.mk.injEq] at h2; exact h2.1.symm
      subst hww
      exact ⟨(canOf π hπ).trans (by rw [hw']), hD⟩
    · have e := kindOf π hπ
      rw [hc', hk] at e
      exact absurd e (by simp [Blocker.kind])
    · have e := kindOf π hπ
      rw [hS', hk] at e
      exact absurd e (by simp [Blocker.kind])
  · -- (e)
    right; right; left
    have hk : role.blocker = .targetResponse := by
      rw [← kindOf π₀ hπ₀, hcw]; rfl
    refine ⟨hk, htc, fun π hπ => ?_⟩
    rcases cls π hπ with ⟨w', hw', -, -⟩ | ⟨w', hw', -, -⟩ | ⟨c', hc', -⟩ | ⟨S', hS', -⟩
    · have e := kindOf π hπ
      rw [hw', hk] at e
      exact absurd e (by simp [Blocker.kind])
    · have e := kindOf π hπ
      rw [hw', hk] at e
      exact absurd e (by simp [Blocker.kind])
    · exact ⟨c', (canOf π hπ).trans (by rw [hc'])⟩
    · have e := kindOf π hπ
      rw [hS', hk] at e
      exact absurd e (by simp [Blocker.kind])
  · -- (f)
    right; right; right
    have hk : role.blocker = .arithmeticChordSet := by
      rw [← kindOf π₀ hπ₀, hS]; rfl
    have allF : ∀ π ∈ pattern, FKind active (explicitCapacity active avoids conn) π token := by
      intro π hπ
      rcases cls π hπ with ⟨w', hw', -, -⟩ | ⟨w', hw', -, -⟩ | ⟨c', hc', -⟩ | ⟨S', hS', hF'⟩
      · have e := kindOf π hπ
        rw [hw', hk] at e
        exact absurd e (by simp [Blocker.kind])
      · have e := kindOf π hπ
        rw [hw', hk] at e
        exact absurd e (by simp [Blocker.kind])
      · have e := kindOf π hπ
        rw [hc', hk] at e
        exact absurd e (by simp [Blocker.kind])
      · exact hF'
    refine ⟨hk, allF, ?_⟩
    obtain ⟨p, q, hp, hq, hpq, hpair, -, hcan, -, -, -, -, -, -, -, htok⟩ := hF
    rcases htok with htp | ⟨v, k, hv, htv⟩
    · left
      refine ⟨p, htp, ?_, ?_⟩
      · intro π hπ
        obtain ⟨p', q', -, -, -, hpair', -, -, -, -, -, -, -, -, -, htok'⟩ := allF π hπ
        rcases htok' with h' | ⟨v', k', -, h'⟩
        · rw [htp] at h'
          simp only [CapacityToken.primitive.injEq, Sum.inr.injEq] at h'
          exact (hpair' p).2 (Or.inl h')
        · rw [htp] at h'; cases h'
      · intro π hπ
        obtain ⟨p', q', -, -, -, -, -, hcan', -, -, -, -, -, -, -, htok'⟩ := allF π hπ
        rcases htok' with h' | ⟨v', k', -, h'⟩
        · rw [htp] at h'
          simp only [CapacityToken.primitive.injEq, Sum.inr.injEq] at h'
          rw [hcan', h']
        · rw [htp] at h'; cases h'
    · right
      refine ⟨v, k, htv, fun π hπ => ?_⟩
      obtain ⟨p', q', -, -, -, hpair', -, hcan', -, -, -, -, -, -, -, htok'⟩ := allF π hπ
      rcases htok' with h' | ⟨v', k', hv', h'⟩
      · rw [htv] at h'; cases h'
      · rw [htv] at h'
        simp only [CapacityToken.remainder.injEq, Prod.mk.injEq] at h'
        obtain ⟨rfl, -⟩ := h'
        exact ⟨p', (hpair' p').2 (Or.inl rfl), hcan', hv'⟩

theorem pairArmARoleAlphabet_holds (pattern : PairArmAPatternStatement data object) :
    PairArmARoleAlphabetStatement data object := by
  intro armA
  classical
  obtain ⟨active, avoids, conn, -, cert, token, role, pattern, -, hov, spec, -, hsub, -, cases⟩ :=
    pattern armA
  clear armA
  refine ⟨_, cert, token, role, hov, hsub, ?_⟩
  rw [hsub]
  rcases cases with ⟨hk, w, htw, -⟩ | ⟨hk, w, htw, -⟩ | ⟨hk, htc, -⟩ | ⟨hk, allF, -⟩
  · rw [hk]
    rcases htw with h | ⟨j, h⟩ <;> rw [h] <;> simp [liveRoles, CapacityToken.subtype]
  · rw [hk]
    rcases htw with h | ⟨j, h⟩ <;> rw [h] <;> simp [liveRoles, CapacityToken.subtype]
  · rw [hk]
    rcases htc with ⟨e, h⟩ | ⟨e, h⟩ | ⟨v, h⟩ | ⟨v, h⟩ <;> rw [h] <;>
      simp [liveRoles, CapacityToken.subtype]
  · rw [hk]
    obtain ⟨-, -, bound, -⟩ := spec
    have hne : pattern.Nonempty := by
      have : 1 ≤ Graph.SameTokenRoutingGerms.patternBound (SurplusRoutingLabel data) := by
        unfold Graph.SameTokenRoutingGerms.patternBound; exact Nat.le_add_left 1 _
      exact Finset.card_pos.1 (lt_of_lt_of_le this bound)
    obtain ⟨π₀, hπ₀⟩ := hne
    obtain ⟨p, q, hp, hq, -, -, -, -, -, -, -, -, -, -, -, htok⟩ := allF π₀ hπ₀
    rcases htok with h | ⟨v, k, -, h⟩ <;> rw [h] <;> simp [liveRoles, CapacityToken.subtype]

/-! ## Arm B -/

theorem pairArmB_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (slack : SlackIndependentStatement data object)
    (above : SurplusAboveStatement data object)
    (switch : HighEndpointSwitchStatement data object) :
    PairArmBStatement data object := by
  have hB1 : PairConditionalFactorizationResidualStatement data object →
      ((∃ system, canonicalPairOverlapSystem data object = some system ∧
        ¬ system.ConditionalFactorization) ∨
      (∃ returns, canonicalPairDemandReturns data object = some returns ∧
        ¬ Graph.ResidualTargetDefect (Graph.HasCycleWithLength data.LengthOK) object
          returns.obstructionCoordinates pairCoordinateSupport ∧
        ¬ PairObstructionHandoff data object returns ∧
        (∀ serial : PairSerialDemandSystem data object, serial.returns ≠ returns) ∧
        (∀ routes : PairDemandReturns.ConnectorRoutes returns,
          (∀ v ∈ routes.forward.support,
            v ∈ returns.overlap.system.overlapSupport returns.overlap.family) →
          (∀ v ∈ routes.forward.support, v ∉ routes.backward.support) →
          routes.forward.length = 0 ∧ routes.backward.length = 0)) ∨
      (∃ serial, canonicalPairSerialSystem data object = some serial ∧
        canonicalPairDemandReturns data object = some serial.returns ∧
        ¬ Graph.ResidualTargetDefect (Graph.HasCycleWithLength data.LengthOK) object
          serial.returns.obstructionCoordinates pairCoordinateSupport ∧
        ¬ PairObstructionHandoff data object serial.returns ∧
        (∀ choice : Fin serial.cells → Nat, (∀ i, choice i ∈ serial.lengths i) →
          ∀ offset ∈ serial.offsets,
            ¬ data.LengthOK (serial.closing + (∑ i, choice i) + offset)))) := by
    intro residual182
    obtain ⟨r⟩ := residual182
    cases r with
    | factorization system hs fails => exact Or.inl ⟨system, hs, fails⟩
    | systemRealizability returns hr fails =>
        obtain ⟨nd, nh, ns, routes⟩ := realizabilityFails_content returns fails
        exact Or.inr (Or.inl ⟨returns, hr, nd, nh, ns, routes⟩)
    | incrementArithmetic serial hs fails =>
        obtain ⟨nd, nh⟩ := incrementFails_content serial fails
        exact Or.inr (Or.inr ⟨serial, hs,
          Contracts.SurplusPair.canonicalPairDemandReturns_of_serial hs, nd, nh,
          fun choice mem offset offMem =>
            serial_lengths_not_accepted serial avoid choice mem offset offMem⟩)
  refine ⟨fun arm => ?_, hB1, fun {returns} hr handoff => ?_, fun {returns} fails routes inside =>
    realizabilityFails_routes_meet returns slack fails routes inside,
    fun {returns} fails => ?_, fun {serial} _hs => ?_⟩
  · obtain ⟨ff, out⟩ := arm
    refine ⟨Contracts.SurplusPair.pairOverlapSystem_of_firstFailure ff noProper, ?_⟩
    rcases out with r | ⟨⟨returns, hr, h⟩, fan⟩
    · rcases hB1 r with i | ⟨returns, hr, nd, -⟩ | ⟨serial, -, hr, nd, -⟩
      · exact Or.inl i
      · exact Or.inr ⟨returns, hr, Or.inl nd⟩
      · exact Or.inr ⟨serial.returns, hr, Or.inl nd⟩
    · exact Or.inr ⟨returns, hr, Or.inr ⟨h, fan⟩⟩
  · obtain ⟨routes, split, envelope, hs, he, -, -, deg, -, nc, ne, a₁, a₂, m, m₁, m₂, esc⟩ :=
      handoff_structure handoff
    refine ⟨Contracts.SurplusPair.typeBFanEntry_of_pairObstructionHandoff above
      ⟨returns, hr, handoff⟩, above, routes, split, envelope, hs, he, ?_, nc, ne, a₁, a₂,
      m, m₁, m₂, esc⟩
    rw [← three]; exact deg
  · by_cases h : returns.leftDemand.2 ∈ returns.overlap.system.overlapSupport
        returns.overlap.family ∧
      returns.rightDemand.1 ∈ returns.overlap.system.overlapSupport returns.overlap.family
    · exact Or.inr ⟨h.1, h.2, exists_U_path returns h.1 h.2,
        fun routes P hP inside =>
          realizabilityFails_path_meets returns slack fails routes P hP inside⟩
    · have o : returns.leftDemand.2 ∉ returns.overlap.system.overlapSupport
            returns.overlap.family ∨
          returns.rightDemand.1 ∉ returns.overlap.system.overlapSupport
            returns.overlap.family := by tauto
      exact Or.inl ⟨o, noSerial_of_end_outside returns o⟩
  · have base : ∀ v, data.threshold ≤ object.degree v :=
      fun v => le_trans baseline (object.minDegree_le_degree v)
    obtain ⟨e₁, e₂⟩ := serial_ends_mem serial
    have c₁ := object.centre_high_of_mem_excessPorts serial.returns.left_active
    have c₂ := object.centre_high_of_mem_excessPorts serial.returns.right_active
    have p₁ := port_end_degree serial.returns.left_active slack base
    have p₂ := port_end_degree serial.returns.right_active slack base
    rw [three] at c₁ c₂ p₁ p₂
    refine ⟨e₁, e₂, c₁, c₂, p₁, p₂,
      fun choice mem offset offMem =>
        serial_lengths_not_accepted serial avoid choice mem offset offMem, ?_⟩
    have := switch serial.returns.leftDemand.1 serial.returns.leftDemand.2 (by rw [three]; exact c₁)
      (by rw [three]; exact p₁) serial.returns.leftDemand_adj
    exact this

end Hypostructure.Graph.Contracts.Spine.PairArms
