import Hypostructure.Graph.CapacityFreeSide.Obstruct
/-!
# Free side, step 2: everything freeness forces on a pair, and the reduction

Generic layer over the live `CapacityPresentation` whose activation is the
recorded blocker activation of an `ActiveSurplusDemands` certificate (this is
exactly `explicitCapacity`).
-/

namespace Hypostructure.Graph.CapacityFreeSide

open Hypostructure Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}} {threshold order : Nat}
  {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}

/-- A pair on the free side of a capacity charge carries no blocker object. -/
theorem blockers_empty_of_freeSide (data : CapacityPresentation object threshold order)
    {pair : Finset (object.Vertex × object.Vertex)}
    (free : pair ∈ freeSide object.vertexPairDecidableEq (object.portPairSchedule threshold)
      data.tokenOrder data.Eligible data.eligibleDecidable) :
    pair ∈ object.portPairSchedule threshold ∧ ¬ (data.activation.blockers pair).Nonempty := by
  classical
  letI := object.vertexPairDecidableEq
  have freeParts := Finset.mem_filter.mp free
  refine ⟨freeParts.1, fun blocked => ?_⟩
  have labelNone := Option.not_isSome_iff_eq_none.mp freeParts.2
  change CanonicalFibreLedger.canonicalLabel
      (FiniteObject.capacityTokenOrder object threshold data.packing)
      (FiniteObject.Charges data.activation data.carrier threshold data.packing)
      pair = none at labelNone
  rw [FiniteObject.canonicalLabel_eq_capacityCharge data.activation
    data.carrier threshold data.packing] at labelNone
  have := FiniteObject.isSome_capacityCharge data.activation data.carrier threshold
    data.packing blocked (data.carrierComplete pair freeParts.1)
  rw [labelNone] at this
  exact Bool.false_ne_true this

/-- A scheduled pair is two distinct selected ports. -/
theorem pair_of_schedule {pair : Finset (object.Vertex × object.Vertex)}
    (mem : pair ∈ object.portPairSchedule threshold) :
    ∃ p q, p ∈ object.excessPorts threshold ∧ q ∈ object.excessPorts threshold ∧
      p ≠ q ∧ ∀ x, x ∈ pair ↔ x = p ∨ x = q := by
  classical
  letI := object.vertexPairDecidableEq
  have sub := object.subset_excessPorts_of_mem_portPairSchedule threshold mem
  have card : pair.card = 2 := by
    unfold FiniteObject.portPairSchedule CanonicalFibreLedger.pairs at mem
    exact (Finset.mem_powersetCard.1 mem).2
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.1 card
  refine ⟨p, q, sub (by simp), sub (by simp), hpq, fun x => ?_⟩
  simp

/-- **Everything freeness forces, at the recorded activation.**  For a pair
`{p,q}` on the free side of the capacity charge:
* (a) the declared supports `T ∪ Γ` are disjoint, hence so are the `T`;
* (b) the canonical returns `R_p`, `R_q` are disjoint, hence the centres differ
  (each `R` ends at its centre) and each endpoint avoids the other return;
* (e) there is no clause-(e) determination obstruction;
* (f) the pair has no chord-set obstruction. -/
theorem unblocked_structure
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (data : CapacityPresentation object threshold order)
    (hact : data.activation = recordSparsePairDEBlockers (Baseline := Baseline)
      (LengthOK := LengthOK) (pairResponseActivation active)
      (object.portPairSchedule threshold))
    {pair : Finset (object.Vertex × object.Vertex)}
    (sched : pair ∈ object.portPairSchedule threshold)
    (noBlk : ¬ (data.activation.blockers pair).Nonempty) :
    ∃ p q, ∃ (hp : p ∈ object.excessPorts threshold) (hq : q ∈ object.excessPorts threshold),
      p ≠ q ∧ (∀ x, x ∈ pair ↔ x = p ∨ x = q) ∧
      Disjoint ((pairResponseActivation active).declaredSupport p)
        ((pairResponseActivation active).declaredSupport q) ∧
      Disjoint (portT hp) (portT hq) ∧
      Disjoint ((pairResponseActivation active).returnSupport p)
        ((pairResponseActivation active).returnSupport q) ∧
      p.1 ≠ q.1 ∧ p.2 ∉ (pairResponseActivation active).returnSupport q ∧
      q.2 ∉ (pairResponseActivation active).returnSupport p ∧
      ¬ SparsePairDEResponseObstructionAt (Baseline := Baseline) (LengthOK := LengthOK)
          (pairResponseActivation active) (object.portPairSchedule threshold) pair ∧
      (pairResponseActivation active).chordObstructions pair = [] := by
  classical
  obtain ⟨p, q, hp, hq, hpq, hpair⟩ := pair_of_schedule sched
  have pm : p ∈ pair := (hpair p).2 (Or.inl rfl)
  have qm : q ∈ pair := (hpair q).2 (Or.inr rfl)
  have blk : ∀ kind, ¬ data.activation.Blocks kind pair := fun kind h =>
    noBlk ((data.activation.exists_blocks_iff_blockers_nonempty pair).1 ⟨kind, h⟩)
  have declEq : data.activation.declaredSupport = (pairResponseActivation active).declaredSupport := by
    rw [hact]; rfl
  have retEq : data.activation.returnSupport = (pairResponseActivation active).returnSupport := by
    rw [hact]; rfl
  have bufEq : data.activation.localBuffer = (pairResponseActivation active).localBuffer := by
    rw [hact]; rfl
  have dD : Disjoint ((pairResponseActivation active).declaredSupport p)
      ((pairResponseActivation active).declaredSupport q) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    rw [← declEq] at h1 h2
    exact blk _ (data.activation.blocks_sharedDeclaredSupport pm qm hpq h1 h2)
  have dR : Disjoint ((pairResponseActivation active).returnSupport p)
      ((pairResponseActivation active).returnSupport q) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    rw [← retEq] at h1 h2
    exact blk _ (data.activation.blocks_sharedReturnSupport pm qm hpq h1 h2)
  have Tsub : ∀ {d} (hd : d ∈ object.excessPorts threshold),
      portT hd ⊆ (pairResponseActivation active).declaredSupport d := by
    intro d hd
    unfold portT
    rw [← pairResponseActivation_localBuffer_of_mem active hd]
    exact FiniteObject.DemandActivation.localBuffer_subset_declaredSupport _ d
  have dT : Disjoint (portT hp) (portT hq) :=
    Finset.disjoint_of_subset_left (Tsub hp) (Finset.disjoint_of_subset_right (Tsub hq) dD)
  have cp := pairResponseActivation_centre_mem_returnSupport_of_mem active hp
  have cq := pairResponseActivation_centre_mem_returnSupport_of_mem active hq
  have ep := pairResponseActivation_endpoint_mem_returnSupport_of_mem active hp
  have eq' := pairResponseActivation_endpoint_mem_returnSupport_of_mem active hq
  refine ⟨p, q, hp, hq, hpq, hpair, dD, dT, dR, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    exact Finset.disjoint_left.1 dR cp (e ▸ cq)
  · exact fun h => Finset.disjoint_left.1 dR ep h
  · exact fun h => Finset.disjoint_right.1 dR eq' h
  · intro obs
    apply blk .targetResponse
    apply data.activation.blocks_targetResponse (coordinate := FiniteObject.DemandActivation.pairCoordinate
      pair (((pairResponseActivation active).pairSupport pair).getD ∅))
    rw [hact]
    simp only [recordSparsePairDEBlockers, if_pos obs, List.mem_singleton]
  · by_contra ne
    obtain ⟨chords, hc⟩ := List.exists_mem_of_ne_nil _ ne
    apply blk .arithmeticChordSet
    apply data.activation.blocks_arithmeticChordSet (chords := chords)
    rw [hact]
    exact hc

theorem free_structure
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (data : CapacityPresentation object threshold order)
    (hact : data.activation = recordSparsePairDEBlockers (Baseline := Baseline)
      (LengthOK := LengthOK) (pairResponseActivation active)
      (object.portPairSchedule threshold))
    {pair : Finset (object.Vertex × object.Vertex)}
    (free : pair ∈ freeSide object.vertexPairDecidableEq (object.portPairSchedule threshold)
      data.tokenOrder data.Eligible data.eligibleDecidable) :
    ∃ p q, ∃ (hp : p ∈ object.excessPorts threshold) (hq : q ∈ object.excessPorts threshold),
      p ≠ q ∧ (∀ x, x ∈ pair ↔ x = p ∨ x = q) ∧
      Disjoint ((pairResponseActivation active).declaredSupport p)
        ((pairResponseActivation active).declaredSupport q) ∧
      Disjoint (portT hp) (portT hq) ∧
      Disjoint ((pairResponseActivation active).returnSupport p)
        ((pairResponseActivation active).returnSupport q) ∧
      p.1 ≠ q.1 ∧ p.2 ∉ (pairResponseActivation active).returnSupport q ∧
      q.2 ∉ (pairResponseActivation active).returnSupport p ∧
      ¬ SparsePairDEResponseObstructionAt (Baseline := Baseline) (LengthOK := LengthOK)
          (pairResponseActivation active) (object.portPairSchedule threshold) pair ∧
      (pairResponseActivation active).chordObstructions pair = [] := by
  obtain ⟨sched, noBlk⟩ := blockers_empty_of_freeSide data free
  exact unblocked_structure active data hact sched noBlk

/-- **The free-side reduction (Lean improvement, not routed by the paper).**
At a minimal, avoiding object on the baseline, every free pair `{p,q}` has a
triangular port or a centre lying in the other port's support:
`Π_free ⊆ Π_tri ∪ Π_cs`. -/
theorem free_triangular_or_centreShoulder
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (data : CapacityPresentation object threshold order)
    (hact : data.activation = recordSparsePairDEBlockers (Baseline := Baseline)
      (LengthOK := LengthOK) (pairResponseActivation active)
      (object.portPairSchedule threshold))
    (baseline : threshold ≤ object.minDegree)
    (minimal : ∀ smaller : FiniteObject.{u}, smaller.LexicographicallySmaller object →
      threshold ≤ smaller.minDegree → HasCycleWithLength LengthOK smaller)
    {pair : Finset (object.Vertex × object.Vertex)}
    (free : pair ∈ freeSide object.vertexPairDecidableEq (object.portPairSchedule threshold)
      data.tokenOrder data.Eligible data.eligibleDecidable) :
    ∃ p q, ∃ (hp : p ∈ object.excessPorts threshold) (hq : q ∈ object.excessPorts threshold),
      p ≠ q ∧ (∀ x, x ∈ pair ↔ x = p ∨ x = q) ∧
      (object.graph.Adj (pairResponseChordEnds active p).1 (pairResponseChordEnds active p).2 ∨
        object.graph.Adj (pairResponseChordEnds active q).1 (pairResponseChordEnds active q).2 ∨
        p.1 ∈ portT hq ∨ q.1 ∈ portT hp) := by
  obtain ⟨p, q, hp, hq, hpq, hpair, -, dT, -, centres, -, -, -, noChord⟩ :=
    free_structure active data hact free
  refine ⟨p, q, hp, hq, hpq, hpair, ?_⟩
  by_contra h
  push Not at h
  obtain ⟨oP, oQ, hpT, hqT⟩ := h
  obtain ⟨chords, hc⟩ := chordObstruction_of_separated active baseline minimal hp hq oP oQ dT
    centres hpT hqT pair hpair
  rw [noChord] at hc
  simp at hc

end Hypostructure.Graph.CapacityFreeSide
