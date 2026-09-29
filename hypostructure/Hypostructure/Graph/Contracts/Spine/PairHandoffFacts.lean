import Hypostructure.Graph.Statements.PairHandoffFacts
import Hypostructure.Graph.Contracts.Spine.PairHandoffSupport

/-!
# Contracts: the structure of G at the pair-obstruction handoff (residual `[187]`)

Contract lemmas for `Statements/PairHandoffFacts.lean`.  Hypotheses are ledger facts: the
handoff support (`PairHandoffSupportStatement`), the extended charge (`ExtFreeEmptyStatement`,
`ExtOverloadedTokenStatement`), the selection's avoidance and minimum-degree baseline, and the
hub facts of the ledger.  One contract per statement: `<statement>_holds`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine.PairHandoffFacts

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph.CapacityFreeSide
open Hypostructure.Graph.SameTokenBlockerRoles

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- A free pair charged by the extended charge is charged to the port token of one of its own
ports. -/
theorem extCharge_port_of_free (c : SurplusCapacity data object)
    {pair : Finset (object.Vertex × object.Vertex)}
    (none' : Graph.FiniteObject.capacityCharge c.activation c.carrier data.threshold c.packing
      pair = none)
    {t : Graph.FiniteObject.CapacityToken object}
    (charged : extCharge data.LengthOK c pair = some t) :
    ∃ port ∈ pair, t = portToken port := by
  classical
  rw [extCharge_of_none data.LengthOK c none'] at charged
  split_ifs at charged with hg hh
  · cases charged
    obtain ⟨c₂, hiff, -⟩ := hg.choose_spec
    exact ⟨_, (hiff _).2 (Or.inl rfl), rfl⟩
  · cases charged
    exact ⟨hh.choose, hh.choose_spec.1, rfl⟩

/-- A pair of the obstruction family has no blocker, hence no old charge. -/
theorem capacityCharge_none_of_family
    {c : SurplusCapacity data object} (hc : canonicalCapacity data object = some c)
    (returns : PairDemandReturns data object)
    {pair : {pair // pair ∈ returns.overlap.system.first.pairSet}} :
    Graph.FiniteObject.capacityCharge c.activation c.carrier data.threshold c.packing
      pair.1 = none := by
  classical
  obtain ⟨⟨active, hact⟩, -⟩ := canonicalCapacity_spec_of_eq_some data object hc
  apply Graph.FiniteObject.capacityCharge_eq_none_of_blockers_eq_empty
  rw [hact]
  exact Finset.not_nonempty_iff_eq_empty.mp
    (returns.overlap.system.first.pairSet_blockerFree pair.1 pair.2)

theorem pairHandoffHubCharge_holds
    (support : PairHandoffSupportStatement data object)
    (free : ExtFreeEmptyStatement data object)
    (newLoadBound : NewLoadBoundStatement data object) :
    PairHandoffHubChargeStatement data object := by
  classical
  obtain ⟨returns, returnsSelected, routes, split, core, centres, hsep, -⟩ := support
  obtain ⟨c, hc, hfree⟩ := free
  obtain ⟨c', hc', hload⟩ := newLoadBound
  have same : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst same
  have charged : ∀ pair ∈ returns.overlap.family, ∃ port ∈ pair.1,
      port ∈ object.excessPorts data.threshold ∧ data.threshold < object.degree port.1 ∧
        extCharge data.LengthOK c' pair.1 = some (portToken port) := by
    intro pair _
    have scheduled := returns.overlap.system.first.pairSet_subset_schedule pair.2
    cases charge : extCharge data.LengthOK c' pair.1 with
    | none =>
        exfalso
        have inFree : pair.1 ∈ extFree data.LengthOK c' :=
          Finset.mem_filter.2 ⟨scheduled, charge⟩
        rw [hfree] at inFree
        simp at inFree
    | some token =>
        obtain ⟨port, portMem, rfl⟩ := extCharge_port_of_free c'
          (capacityCharge_none_of_family hc' returns) charge
        have inPorts := object.subset_excessPorts_of_mem_portPairSchedule data.threshold
          scheduled portMem
        exact ⟨port, portMem, inPorts,
          Graph.FiniteObject.centre_high_of_mem_excessPorts inPorts, rfl⟩
  refine ⟨returns, returnsSelected, routes, split, hsep, c', hc', charged, ?_, ?_⟩
  · -- the ports at `h`
    have eq : (object.excessPorts data.threshold).filter
          (fun port => port.1 = split.separator) =
        ((object.selectedPortEndpoints data.threshold split.separator).toFinset.image
          fun endpoint => (split.separator, endpoint)) := by
      ext port
      simp only [Finset.mem_filter, Finset.mem_image, List.mem_toFinset,
        Graph.FiniteObject.mem_excessPorts_iff]
      constructor
      · rintro ⟨mem, h⟩
        exact ⟨port.2, by rw [← h]; exact mem, Prod.ext h.symm rfl⟩
      · rintro ⟨endpoint, mem, rfl⟩
        exact ⟨mem, rfl⟩
    rw [eq, Finset.card_image_of_injective _ (fun _ _ e => congrArg Prod.snd e),
      List.toFinset_card_of_nodup (Graph.FiniteObject.selectedPortEndpoints_nodup _),
      Graph.FiniteObject.selectedPortEndpoints_length]
  · -- the load on the tokens of `h`
    set ports := (object.excessPorts data.threshold).filter
      (fun port => port.1 = split.separator) with hports
    let target : Finset (Finset (object.Vertex × object.Vertex)) :=
      ports.biUnion fun port =>
        (object.portPairSchedule data.threshold).filter fun pair =>
          Graph.FiniteObject.capacityCharge c'.activation c'.carrier data.threshold c'.packing
            pair = none ∧ extCharge data.LengthOK c' pair = some (portToken port)
    have image : ((returns.overlap.family.filter (fun pair => ∃ port ∈ pair.1,
        port.1 = split.separator ∧
          extCharge data.LengthOK c' pair.1 = some (portToken port))).image Subtype.val) ⊆
        target := by
      intro pair member
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp member
      obtain ⟨hpFamily, port, portMem, portCentre, charge⟩ := Finset.mem_filter.mp hp
      have inPorts' := object.subset_excessPorts_of_mem_portPairSchedule data.threshold
        (returns.overlap.system.first.pairSet_subset_schedule p.2) portMem
      refine Finset.mem_biUnion.mpr ⟨port, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨inPorts', portCentre⟩
      · exact Finset.mem_filter.mpr ⟨returns.overlap.system.first.pairSet_subset_schedule p.2,
          capacityCharge_none_of_family hc' returns, charge⟩
    calc (returns.overlap.family.filter (fun pair => ∃ port ∈ pair.1,
          port.1 = split.separator ∧
            extCharge data.LengthOK c' pair.1 = some (portToken port))).card
        = ((returns.overlap.family.filter (fun pair => ∃ port ∈ pair.1,
          port.1 = split.separator ∧
            extCharge data.LengthOK c' pair.1 = some (portToken port))).image Subtype.val).card :=
          (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ ≤ target.card := Finset.card_le_card image
      _ ≤ ∑ port ∈ ports, newLoad data.LengthOK c' port :=
          Finset.card_biUnion_le.trans (le_of_eq rfl)
      _ ≤ _ := Finset.sum_le_sum fun port member =>
          hload port (Finset.mem_filter.mp member).1

theorem pairHandoffBoundaryType_holds
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (support : PairHandoffSupportStatement data object) :
    PairHandoffBoundaryTypeStatement data object := by
  classical
  obtain ⟨returns, returnsSelected, routes, split, core, centres, _hsep, _hsup, _coreEq,
    centresEq, _nonempty, high, _coreInU, centresInU⟩ := support
  have separatorMem : split.separator ∈
      returns.overlap.system.overlapSupport returns.overlap.family :=
    centresInU split.separator (by rw [centresEq]; exact Finset.mem_singleton_self _)
  have separatorHigh : data.threshold < object.degree split.separator :=
    high split.separator (by rw [centresEq]; exact Finset.mem_singleton_self _)
  set U := returns.overlap.system.overlapSupport returns.overlap.family with hU
  have vertexBaseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
    fun vertex => baseline.trans (object.minDegree_le_degree vertex)
  refine ⟨returns, returnsSelected, U, rfl, ⟨split.separator, separatorMem⟩,
    returns.overlap.connected, ?_, ?_, ?_, fun X => ActualContext.not_target_actualGlue avoids U X⟩
  · unfold Graph.FiniteObject.boundaryIncidence
    symm
    apply Finset.sum_filter_of_ne
    intro vertex _ nonzero
    exact Nat.sub_ne_zero_iff_lt.mp nonzero
  · rw [object.boundaryIncidence_eq_sub U]
    have le : ∑ vertex ∈ U, object.internalDegree U vertex ≤ ∑ vertex ∈ U, object.degree vertex :=
      Finset.sum_le_sum fun vertex _ => object.internalDegree_le_degree U vertex
    rw [Nat.sub_add_cancel le]
    exact Graph.FiniteObject.sum_degree_eq_threshold_mul_card_add_ambientSurplus object U
      data.threshold vertexBaseline
  · have single : object.degree split.separator - data.threshold ≤
        object.ambientSurplus U data.threshold :=
      Finset.single_le_sum (f := fun vertex => object.degree vertex - data.threshold)
        (fun _ _ => Nat.zero_le _) separatorMem
    omega

open Classical in
theorem exists_critical_order
    {LengthOK : Nat → Prop} {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {schedule : Finset (Finset (object.Vertex × object.Vertex))}
    (model : Graph.SparsePairSkeletonModel activation schedule)
    (F : Finset {pair // pair ∈ model.pairSet})
    (π : {pair // pair ∈ model.pairSet}) (hπ : π ∈ F)
    (peel : model.RealizingOrder (LengthOK := LengthOK) (F.erase π))
    (notReal : ¬ model.RealizingOrder (LengthOK := LengthOK) F) :
    ∃ (order : Fin F.card ≃ {pair // pair ∈ F}) (level : Nat) (bound : level ≤ F.card)
      (last : level < F.card), F.card = level + 1 ∧ (order ⟨level, last⟩).1 = π ∧
      model.signatureCount (LengthOK := LengthOK) F order level bound =
        2 ^ level * model.signatureCount (LengthOK := LengthOK) F order 0 (Nat.zero_le _) ∧
      model.signatureCount (LengthOK := LengthOK) F order F.card le_rfl <
        2 * model.signatureCount (LengthOK := LengthOK) F order level bound := by
  classical
  obtain ⟨sigma, hsigma⟩ := peel
  have hcard : F.card = (F.erase π).card + 1 := (Finset.card_erase_add_one hπ).symm
  let f : Fin F.card → {p // p ∈ F} := fun i =>
    if h : i.1 < (F.erase π).card then ⟨(sigma ⟨i.1, h⟩).1, Finset.mem_of_mem_erase (sigma ⟨i.1, h⟩).2⟩
    else ⟨π, hπ⟩
  have inj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    by_cases hi : i.1 < (F.erase π).card <;> by_cases hj : j.1 < (F.erase π).card
    · simp only [f, dif_pos hi, dif_pos hj] at hij
      have e1 := Subtype.mk.inj hij
      have e2 : sigma ⟨i.1, hi⟩ = sigma ⟨j.1, hj⟩ := Subtype.ext e1
      exact Fin.mk.inj (sigma.injective e2)
    · simp only [f, dif_pos hi, dif_neg hj] at hij
      exact absurd (Subtype.mk.inj hij) (Finset.ne_of_mem_erase (sigma ⟨i.1, hi⟩).2)
    · simp only [f, dif_neg hi, dif_pos hj] at hij
      exact absurd (Subtype.mk.inj hij).symm (Finset.ne_of_mem_erase (sigma ⟨j.1, hj⟩).2)
    · have := i.2; have := j.2; omega
  have bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨inj, by simp⟩
  let tau := Equiv.ofBijective f bij
  have agree : ∀ (k : Nat) (b : k ≤ F.card) (b' : k ≤ (F.erase π).card) (index : Fin k),
      (tau (Fin.castLE b index)).1 = (sigma (Fin.castLE b' index)).1 := by
    intro k b b' index
    have lt : (Fin.castLE b index).1 < (F.erase π).card := lt_of_lt_of_le index.2 b'
    show (f (Fin.castLE b index)).1 = _
    simp only [f, dif_pos lt]
    rfl
  have prefixEq : ∀ (k : Nat) (b : k ≤ F.card) (b' : k ≤ (F.erase π).card),
      model.signatureCount (LengthOK := LengthOK) F tau k b =
        model.signatureCount (LengthOK := LengthOK) (F.erase π) sigma k b' :=
    fun k b b' => model.signatureCount_congr F (F.erase π) tau sigma k b b' (agree k b b')
  have lastLt : (F.erase π).card < F.card := by omega
  have atLevel : model.signatureCount (LengthOK := LengthOK) F tau (F.erase π).card (by omega) =
      2 ^ (F.erase π).card * model.signatureCount (LengthOK := LengthOK) F tau 0 (Nat.zero_le _) := by
    rw [prefixEq (F.erase π).card (by omega) le_rfl, prefixEq 0 (Nat.zero_le _) (Nat.zero_le _)]
    exact hsigma
  have upper := model.signatureCount_le_two_mul (LengthOK := LengthOK) F tau (F.erase π).card F.card hcard
    le_rfl (by omega)
  have notEq : model.signatureCount (LengthOK := LengthOK) F tau F.card le_rfl ≠
      2 ^ F.card * model.signatureCount (LengthOK := LengthOK) F tau 0 (Nat.zero_le _) :=
    fun equal => notReal ⟨tau, equal⟩
  refine ⟨tau, (F.erase π).card, by omega, lastLt, hcard, ?_, atLevel, ?_⟩
  · show (f ⟨(F.erase π).card, lastLt⟩).1 = π
    simp [f]
  · have doubled : 2 * model.signatureCount (LengthOK := LengthOK) F tau (F.erase π).card (by omega) =
        2 ^ F.card * model.signatureCount (LengthOK := LengthOK) F tau 0 (Nat.zero_le _) := by
      have pw : 2 ^ F.card = 2 ^ (F.erase π).card * 2 := by rw [hcard, pow_succ]
      rw [atLevel, pw]; ring
    have ne' : model.signatureCount (LengthOK := LengthOK) F tau F.card le_rfl ≠
        2 * model.signatureCount (LengthOK := LengthOK) F tau (F.erase π).card (by omega) := by
      rw [doubled]; exact notEq
    exact lt_of_le_of_ne upper ne'

theorem pairHandoffCriticalCoordinate_holds
    (support : PairHandoffSupportStatement data object) :
    PairHandoffCriticalCoordinateStatement data object := by
  classical
  obtain ⟨returns, returnsSelected, routes, split, core, centres, hsep, -, -, centresEq,
    -, -, -, centresInU⟩ := support
  refine ⟨returns, returnsSelected, ?_, routes, split, hsep, ?_⟩
  · intro pair member
    have two : 2 ≤ returns.overlap.family.card := by
      obtain ⟨left, leftMem, right, rightMem, different, -⟩ :=
        returns.overlap.overlapWitness
      exact Finset.one_lt_card.mpr ⟨left, leftMem, right, rightMem, different⟩
    have nonempty : (returns.overlap.family.erase pair).Nonempty :=
      Finset.card_pos.mp (by rw [Finset.card_erase_of_mem member]; omega)
    exact exists_critical_order returns.overlap.system.toSkeletonModel returns.overlap.family
      pair member (returns.overlap.minimal.2 _ (Finset.erase_ssubset member) nonempty)
      returns.overlap.minimal.1.2
  · intro vertex cases'
    obtain ⟨rspec, sspec⟩ := PairArms.pairObstructionSeparator_spec_of_eq_some hsep
    have inU : vertex ∈ returns.overlap.system.overlapSupport returns.overlap.family := by
      rcases cases' with rfl | rfl | rfl
      · exact centresInU _ (by rw [centresEq]; exact Finset.mem_singleton_self _)
      · have hmem : split.nextFirst ∈ routes.first := by rw [sspec.1]; simp
        exact PairArms.mem_route_of_route rspec.2.2.1 hmem
      · have hmem : split.nextSecond ∈ routes.second := by rw [sspec.2.1]; simp
        exact PairArms.mem_route_of_route rspec.2.2.2.1 hmem
    have inUnion : ∃ pair ∈ returns.overlap.family,
        vertex ∈ returns.overlap.system.responseSupport pair := by
      unfold PairOverlapSystem.overlapSupport Graph.SparsePairSkeletonModel.responseSupportUnion
        at inU
      exact Finset.mem_biUnion.mp inU
    obtain ⟨pair, pairMem, vertexMem⟩ := inUnion
    obtain ⟨chosen, selected, chosenMem, chosenVertex⟩ :=
      canonicalChoice_spec (spec := fun pair : {pair // pair ∈
          returns.overlap.system.first.pairSet} => pair ∈ returns.overlap.family ∧
            vertex ∈ returns.overlap.system.responseSupport pair)
        ⟨pair, pairMem, vertexMem⟩
    exact ⟨chosen, selected, chosenMem, chosenVertex⟩

theorem pairObstructionDescent_holds
    (support : PairHandoffSupportStatement data object) :
    PairObstructionDescentStatement data object := by
  classical
  obtain ⟨returns, returnsSelected, -⟩ := support
  refine ⟨returns, returnsSelected, ?_, ?_, returns.overlap.minimal.1.2, ?_⟩
  · obtain ⟨left, leftMem, right, rightMem, different, -⟩ := returns.overlap.overlapWitness
    exact Finset.one_lt_card.mpr ⟨left, leftMem, right, rightMem, different⟩
  · calc returns.overlap.family.card ≤ Fintype.card
          {pair // pair ∈ returns.overlap.system.first.pairSet} := Finset.card_le_univ _
      _ = returns.overlap.system.first.pairSet.card := Fintype.card_coe _
  · intro member memberMem nonempty
    exact returns.overlap.minimal.2 _ (Finset.erase_ssubset memberMem) nonempty

theorem pairHandoffHubForces_holds
    (support : PairHandoffSupportStatement data object)
    (split : HighCentreSplitForcedStatement data object)
    (switch : SameVertexSwitchForcedPathStatement data object)
    (endpoint : HighEndpointSwitchStatement data object)
    (fan : ThreeRouteFanStatement object) (chain : ThreeRouteChainStatement object) :
    PairHandoffHubForcesStatement data object := by
  obtain ⟨returns, returnsSelected, routes, separator, core, centres, hsep, _hsup, _coreEq,
    centresEq, _nonempty, high, _coreInU, _centresInU⟩ := support
  have separatorHigh : data.threshold < object.degree separator.separator :=
    high separator.separator (by rw [centresEq]; exact Finset.mem_singleton_self _)
  refine ⟨returns, returnsSelected, routes, separator, hsep, split separator.separator separatorHigh,
    fun u₁ u₂ a₁ a₂ ne nadj deg => switch a₁ a₂ ne nadj deg, ?_,
    @fan separator.separator, @chain separator.separator⟩
  intro c cubic adj
  exact endpoint separator.separator c (by omega) cubic adj

end Hypostructure.Graph.Contracts.Spine.PairHandoffFacts
