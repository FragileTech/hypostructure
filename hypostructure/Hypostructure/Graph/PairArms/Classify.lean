import Hypostructure.Graph.PairArms.Kinds

/-!
# Arm A, generic layer (cont.): the four surviving blocker kinds of a charged pair

At a capacity presentation whose activation is the recorded blocker activation of an
`ActiveSurplusDemands` certificate , every pair
the ledger charges to a token `t` is in exactly one of four cases:

* **(a)** canonical blocker `sharedDeclaredSupport (vertex w)`, `t ∈ {V(w), R(w,j)}`, and
  `w ∈ T(d) ∪ Γ(d)` for both ports `d` of the pair;
* **(b)** canonical blocker `sharedReturnSupport (vertex w)`, `t ∈ {V(w), R(w,j)}`, and
  `w ∈ R_d` for both ports;
* **(e)** canonical blocker `targetResponse c`, `t ∈ 𝔗_W ∪ 𝔗_R ∪ V`;
* **(f)** canonical blocker the singleton `{p}` of the chord-earlier port, the pair fully
  separated, `t ∈ {P(p)} ∪ {R(v,k) : v a shoulder of p}`.

Clauses (c) and (d) never occur, and no pair is ever charged to an incidence token.
Also: a pattern (matching or star) of 2-sets covers at least `|pattern| + 1` ports.
-/

namespace Hypostructure.Graph.PairArms

open Hypostructure Hypostructure.Graph Hypostructure.Graph.FiniteObject

universe u v

/-! ## Patterns cover many ports -/

section pattern

variable {V : Type u} [DecidableEq V]

/-- **A nonempty matching or star of 2-sets covers at least `|P| + 1` vertices.** -/
theorem card_support_ge (P : Finset (Finset V)) (h2 : ∀ π ∈ P, π.card = 2)
    (hne : P.Nonempty)
    (hms : PatternFamily.IsMatching P ∨ ∃ c, PatternFamily.IsStar P c) :
    P.card + 1 ≤ (PatternFamily.support P).card := by
  classical
  unfold PatternFamily.support
  rcases hms with hm | ⟨c, hc⟩
  · rw [Finset.card_biUnion]
    · have : ∑ π ∈ P, (id π).card = ∑ _π ∈ P, 2 := Finset.sum_congr rfl fun π hπ => h2 π hπ
      rw [this, Finset.sum_const, smul_eq_mul]
      have := hne.card_pos
      omega
    · intro π hπ π' hπ' hne'
      rw [Function.onFun, Finset.disjoint_left]
      intro x hx hx'
      exact hm π hπ π' hπ' hne' x hx hx'
  · -- the leaves `π.erase c` are pairwise disjoint singletons inside `support.erase c`
    have hcm : c ∈ P.biUnion id := by
      obtain ⟨π, hπ⟩ := hne
      exact Finset.mem_biUnion.2 ⟨π, hπ, hc π hπ⟩
    have hleaf : ∀ π ∈ P, (π.erase c).card = 1 := by
      intro π hπ
      rw [Finset.card_erase_of_mem (hc π hπ), h2 π hπ]
    have hdisj : ∀ π ∈ P, ∀ π' ∈ P, π ≠ π' → Disjoint (π.erase c) (π'.erase c) := by
      intro π hπ π' hπ' hne'
      rw [Finset.disjoint_left]
      intro x hx hx'
      apply hne'
      have hxc : x ≠ c := Finset.ne_of_mem_erase hx
      have e1 : π = {c, x} := by
        apply Finset.eq_of_subset_of_card_le
        · intro y hy
          by_cases hyc : y = c
          · simp [hyc]
          · have hy1 : y ∈ π.erase c := Finset.mem_erase.2 ⟨hyc, hy⟩
            obtain ⟨z, hz⟩ := Finset.card_eq_one.1 (hleaf π hπ)
            rw [hz] at hy1 hx
            simp only [Finset.mem_singleton] at hy1 hx
            simp [hy1, hx]
        · rw [Finset.card_pair hxc.symm, h2 π hπ]
      have e2 : π' = {c, x} := by
        apply Finset.eq_of_subset_of_card_le
        · intro y hy
          by_cases hyc : y = c
          · simp [hyc]
          · have hy1 : y ∈ π'.erase c := Finset.mem_erase.2 ⟨hyc, hy⟩
            obtain ⟨z, hz⟩ := Finset.card_eq_one.1 (hleaf π' hπ')
            rw [hz] at hy1 hx'
            simp only [Finset.mem_singleton] at hy1 hx'
            simp [hy1, hx']
        · rw [Finset.card_pair hxc.symm, h2 π' hπ']
      rw [e1, e2]
    have hsub : P.biUnion (fun π => π.erase c) ⊆ (P.biUnion id).erase c := by
      intro x hx
      obtain ⟨π, hπ, hx⟩ := Finset.mem_biUnion.1 hx
      exact Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hx,
        Finset.mem_biUnion.2 ⟨π, hπ, Finset.mem_of_mem_erase hx⟩⟩
    have hcard : (P.biUnion fun π => π.erase c).card = P.card := by
      rw [Finset.card_biUnion (fun π hπ π' hπ' h => hdisj π hπ π' hπ' h)]
      rw [Finset.sum_congr rfl hleaf, Finset.sum_const, smul_eq_mul, mul_one]
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hcm] at this
    have hpos : 0 < (P.biUnion id).card := Finset.card_pos.2 ⟨c, hcm⟩
    omega

end pattern

/-! ## Charged pairs -/

section charged

variable {object : FiniteObject.{u}} {Coordinate Chord : Type v}

/-- A charged pair has a canonical blocker. -/
theorem canonical_of_charge (activation : DemandActivation object Coordinate Chord)
    (presentation : CarrierPresentation object Coordinate Chord) (threshold : Nat)
    (packing : Finset (Finset object.Vertex)) {pair : Finset (object.Vertex × object.Vertex)}
    {t : CapacityToken object}
    (h : capacityCharge activation presentation threshold packing pair = some t) :
    ∃ b, canonicalBlocker activation pair = some b := by
  classical
  rcases hb : canonicalBlocker activation pair with _ | b
  · exfalso
    have hs : chargeSupport activation presentation pair = ∅ := by
      simp [chargeSupport, hb]
    unfold capacityCharge windowJoinChoice crossWindowChoice remainderVertexChoice at h
    simp [hs, hb] at h
  · exact ⟨b, rfl⟩

/-- Clause (d) is never canonical when the activation lists no profile obstruction. -/
theorem canonical_ne_profile (activation : DemandActivation object Coordinate Chord)
    (pair : Finset (object.Vertex × object.Vertex))
    (hA : activation.profileObstructions pair = []) (c : Coordinate) :
    canonicalBlocker activation pair ≠ some (Blocker.boundaryProfile c) := by
  classical
  intro h
  have hm := canonicalBlocker_mem activation h
  unfold DemandActivation.blockers at hm
  simp [hA] at hm

end charged

section recorded

variable {object : FiniteObject.{u}} {threshold order : Nat}
  {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}

open Hypostructure.Graph.CapacityFreeSide

/-- **The clause-(f) structure of a pair**: `{p,q}`, `p` before `q` in chord order,
canonical blocker `{p}`, both ports open, fully separated, and the charge `t` is the
port token `p` or a remainder unit at a shoulder of `p`. -/
def FKind (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (data : CapacityPresentation object threshold order)
    (pair : Finset (object.Vertex × object.Vertex)) (t : CapacityToken object) : Prop :=
  ∃ p q, ∃ (hp : p ∈ object.excessPorts threshold) (hq : q ∈ object.excessPorts threshold),
    p ≠ q ∧ (∀ x, x ∈ pair ↔ x = p ∨ x = q) ∧
    (∃ A B, chordOrder active = A ++ p :: B ∧ q ∉ A) ∧
    canonicalBlocker data.activation pair = some (Blocker.arithmeticChordSet {p}) ∧
    ¬ object.graph.Adj (pairResponseChordEnds active p).1 (pairResponseChordEnds active p).2 ∧
    ¬ object.graph.Adj (pairResponseChordEnds active q).1 (pairResponseChordEnds active q).2 ∧
    Disjoint ((pairResponseActivation active).declaredSupport p)
      ((pairResponseActivation active).declaredSupport q) ∧
    Disjoint ((pairResponseActivation active).returnSupport p)
      ((pairResponseActivation active).returnSupport q) ∧
    Disjoint (portT hp) (portT hq) ∧ p.1 ∉ portT hq ∧ q.1 ∉ portT hp ∧
    (t = .primitive (.inr (.inr p)) ∨
      ∃ v k, (v = (pairResponseChordEnds active p).1 ∨
          v = (pairResponseChordEnds active p).2) ∧ t = .remainder (v, k))

/-- **Classification of a charged pair at the recorded activation.** -/
theorem pair_classification
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (data : CapacityPresentation object threshold order)
    (hact : data.activation = recordSparsePairDEBlockers (Baseline := Baseline)
      (LengthOK := LengthOK) (pairResponseActivation active)
      (object.portPairSchedule threshold))
    (avoids : ¬ HasCycleWithLength LengthOK object)
    {pair : Finset (object.Vertex × object.Vertex)}
    (hsched : pair ∈ object.portPairSchedule threshold)
    {t : CapacityToken object} {b : Blocker object object.PairCoordinate
      (object.Vertex × object.Vertex)}
    (hcharge : capacityCharge data.activation data.carrier threshold data.packing pair = some t)
    (hb : canonicalBlocker data.activation pair = some b) :
    (∃ w, b = .sharedDeclaredSupport (.vertex w) ∧
        (t = .primitive (.inl w) ∨ ∃ j, t = .remainder (w, j)) ∧
        ∀ d ∈ pair, w ∈ data.activation.declaredSupport d) ∨
      (∃ w, b = .sharedReturnSupport (.vertex w) ∧
        (t = .primitive (.inl w) ∨ ∃ j, t = .remainder (w, j)) ∧
        ∀ d ∈ pair, w ∈ data.activation.returnSupport d) ∨
      (∃ c, b = .targetResponse c ∧
        ((∃ e, t = .boundaryWindow e) ∨ (∃ e, t = .crossWindow e) ∨
          (∃ v, t = .remainder v) ∨ (∃ v, t = .primitive (.inl v)))) ∨
      (∃ S, b = .arithmeticChordSet S ∧ FKind active data pair t) := by
  classical
  obtain ⟨p, q, -, -, hpq, hpair⟩ := pair_of_schedule hsched
  have both : ∀ {l r d : object.Vertex × object.Vertex}, l ∈ pair → r ∈ pair → l ≠ r →
      d ∈ pair → d = l ∨ d = r := by
    intro l r d hl hr hlr hd
    rw [hpair] at hl hr hd
    rcases hl with rfl | rfl <;> rcases hr with rfl | rfl <;> rcases hd with rfl | rfl <;>
      simp_all
  cases b with
  | sharedDeclaredSupport item =>
      cases item with
      | vertex w =>
          left
          refine ⟨w, rfl, ?_, ?_⟩
          · rcases Hypostructure.Graph.WindowChargeKinds.early_charge data.carrier data.activation threshold
              data.packing (Or.inl hb) with ⟨j, hj⟩ | hj
            · rw [hcharge] at hj; exact Or.inr ⟨j, Option.some.inj hj⟩
            · rw [hcharge] at hj; exact Or.inl (Option.some.inj hj)
          · have hm := canonicalBlocker_mem data.activation hb
            rw [DemandActivation.sharedDeclaredSupport_mem_blockers_iff] at hm
            obtain ⟨l, hl, r, hr, hlr, hs⟩ := hm
            have hw := DemandActivation.mem_both_of_vertex_mem_sharedItems hs
            intro d hd
            rcases both hl hr hlr hd with rfl | rfl
            · exact hw.1
            · exact hw.2
      | incidence e =>
          exact absurd hb
            (Hypostructure.Graph.WindowChargeKinds.canonicalBlocker_ne_sharedDeclared_incidence _ _ e)
  | sharedReturnSupport item =>
      cases item with
      | vertex w =>
          right; left
          refine ⟨w, rfl, ?_, ?_⟩
          · rcases Hypostructure.Graph.WindowChargeKinds.early_charge data.carrier data.activation threshold
              data.packing (Or.inr hb) with ⟨j, hj⟩ | hj
            · rw [hcharge] at hj; exact Or.inr ⟨j, Option.some.inj hj⟩
            · rw [hcharge] at hj; exact Or.inl (Option.some.inj hj)
          · have hm := canonicalBlocker_mem data.activation hb
            rw [DemandActivation.sharedReturnSupport_mem_blockers_iff] at hm
            obtain ⟨l, hl, r, hr, hlr, hs⟩ := hm
            have hw := DemandActivation.mem_both_of_vertex_mem_sharedItems hs
            intro d hd
            rcases both hl hr hlr hd with rfl | rfl
            · exact hw.1
            · exact hw.2
      | incidence e =>
          exact absurd hb
            (Hypostructure.Graph.WindowChargeKinds.canonicalBlocker_ne_sharedReturn_incidence _ _ e)
  | sharedLocalBuffer w =>
      exact absurd hb (canonicalBlocker_ne_localBuffer _ _ w)
  | boundaryProfile c =>
      refine absurd hb (canonical_ne_profile _ _ ?_ c)
      rw [hact]
      exact Hypostructure.Graph.WindowChargeKinds.recorded_profile_empty active _ pair
  | targetResponse c =>
      right; right; left
      exact ⟨c, rfl, eKind_charge_subtype data.activation data.carrier threshold data.packing
        hb hcharge⟩
  | arithmeticChordSet S =>
      right; right; right
      refine ⟨S, rfl, ?_⟩
      obtain ⟨p, q, hp, hq, hpq, hpair, hord, hS, openP, openQ, dD, dR, dT, hpT, hqT, hch⟩ :=
        fKind_charge active data hact avoids hsched hb
      subst hS
      refine ⟨p, q, hp, hq, hpq, hpair, hord, hb, openP, openQ, dD, dR, dT, hpT, hqT, ?_⟩
      rcases hch with h | ⟨v, k, hv, h⟩
      · rw [hcharge] at h; exact Or.inl (Option.some.inj h)
      · rw [hcharge] at h; exact Or.inr ⟨v, k, hv, Option.some.inj h⟩

end recorded

end Hypostructure.Graph.PairArms
