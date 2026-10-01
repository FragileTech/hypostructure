import Hypostructure.Graph.Statements.PairHandoffSupport
import Hypostructure.Graph.Contracts.Spine.PairArms
import Hypostructure.Graph.Contracts.SurplusPair.PairCode

/-!
# Contracts: the Type B support of G's pair-obstruction handoff (residual `[187]`)

Contract lemmas for `Statements/PairHandoffSupport.lean`.  The hypothesis is the first-separator
handoff of G's retained pair obstruction, exactly what the `[179]`/`[180]` early rows derive
from the early outcome, the selection and the sparse-survivor fact; the charge contract also
reads `K .portEndDegree`.  One contract per statement: `<statement>_holds`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine.PairHandoffSupport

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- **Lean improvement: the `[180]` periodic alternatives are empty after `[179]`'s no-early
arm.**  G's canonical serial system is built on G's canonical returns
(`canonicalPairDemandReturns_of_serial`), and the periodic alternative of `[180]` (the
obstruction's first-separator handoff) is the same-named alternative of `[179]`'s early outcome
at those returns.  So `[180]`'s early outcome refutes `[179]`'s
no-early arm, at G. -/
theorem not_pairIncrementEarly_of_noEarly
    (noEarly : PairSystemNoEarlyOutcomeStatement data object)
    (early : PairIncrementEarlyOutcomeStatement data object) : False := by
  obtain ⟨returns, returnsSelected, none⟩ := noEarly
  obtain ⟨serial, serialSelected, ⟨outcome⟩⟩ := early
  have same : serial.returns = returns :=
    Option.some.inj
      ((Graph.Contracts.SurplusPair.canonicalPairDemandReturns_of_serial serialSelected).symm.trans
        returnsSelected)
  subst same
  cases outcome with
  | typeB handoff => exact none ⟨.typeB handoff⟩

/-- The canonical envelope of the obstruction is `envelopeOfFirstSeparator` on the core
`{d_p.2, d_q.2}` with the one decoration `{h}`. -/
theorem pairObstructionEnvelope_shape
    {returns : PairDemandReturns data object}
    {routes : PairObstructionRoutes object} {split : SameTokenFirstSeparator object}
    {envelope : SameTokenEnvelope data object}
    (selected : canonicalPairObstructionSeparator data object returns =
      some (routes, split))
    (env : canonicalPairObstructionEnvelope data object returns = some envelope) :
    envelope.core = pairObstructionCore data object returns ∧
      envelope.decorations = {split.separator} := by
  classical
  unfold canonicalPairObstructionEnvelope at env
  rw [selected] at env
  simp only at env
  split at env
  · next both =>
    have same := Option.some.inj env
    subst same
    exact ⟨rfl, rfl⟩
  · cases env

theorem pairHandoffSupport_holds
    (handoff : ∃ returns, canonicalPairDemandReturns data object = some returns ∧
      PairObstructionHandoff data object returns) :
    PairHandoffSupportStatement data object := by
  classical
  obtain ⟨returns, returnsSelected, core, centres, atSupport⟩ := handoff
  obtain ⟨⟨core', centres'⟩, supportSelected, at'⟩ :=
    canonicalChoice_spec
      (spec := fun support : Finset object.Vertex × Finset object.Vertex =>
        PairObstructionHandoffAt data object returns support.1 support.2)
      ⟨(core, centres), atSupport⟩
  obtain ⟨routes, split, envelope, hsep, henv, _escape, hcore, hdec⟩ := at'
  obtain ⟨rspec, sspec⟩ := PairArms.pairObstructionSeparator_spec_of_eq_some hsep
  have cond := PairArms.pairObstructionEnvelope_conditions hsep henv
  obtain ⟨shapeCore, shapeDec⟩ := pairObstructionEnvelope_shape hsep henv
  have coreEq : core' = pairObstructionCore data object returns :=
    hcore.symm.trans shapeCore
  have centresEq : centres' = {split.separator} := hdec.symm.trans shapeDec
  have inU : ∀ {path : List object.Vertex} {endpoint : object.Vertex},
      PairObstructionRoute data object returns path endpoint →
      endpoint ∈ returns.overlap.system.overlapSupport returns.overlap.family :=
    fun route => route.2.2.2 _ (List.mem_of_getLast? route.2.2.1)
  refine ⟨returns, returnsSelected, routes, split, core', centres', hsep, supportSelected,
    coreEq, centresEq, ?_, ?_, ?_, ?_⟩
  · rw [centresEq]; exact Finset.singleton_nonempty _
  · intro centre member
    rw [centresEq, Finset.mem_singleton] at member
    subst member
    exact cond.1
  · intro vertex member
    rw [coreEq] at member
    unfold pairObstructionCore at member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact inU rspec.2.2.1
    · exact inU rspec.2.2.2.1
  · intro vertex member
    rw [centresEq, Finset.mem_singleton] at member
    subst member
    have hmem : split.separator ∈ routes.first := by
      rw [sspec.1]; simp
    exact rspec.2.2.1.2.2.2 _ hmem

theorem pairHandoffCharge_holds
    (ports : PortEndDegreeStatement data object)
    (handoff : ∃ returns, canonicalPairDemandReturns data object = some returns ∧
      PairObstructionHandoff data object returns) :
    PairHandoffChargeStatement data object := by
  classical
  obtain ⟨returns, returnsSelected, routes, split, core, centres, _hsep, supportSelected,
    coreEq, centresEq, _nonempty, high, _coreInU, _centresInU⟩ :=
    pairHandoffSupport_holds handoff
  have coreDegree : ∀ vertex ∈ core, object.degree vertex = data.threshold := by
    intro vertex member
    rw [coreEq] at member
    unfold pairObstructionCore at member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact ports _ returns.left_active
    · exact ports _ returns.right_active
  have centreHigh : data.threshold < object.degree split.separator :=
    high split.separator (by rw [centresEq]; exact Finset.mem_singleton_self _)
  refine ⟨returns, returnsSelected, core, centres, supportSelected, coreDegree, ?_, ?_, ?_, ?_⟩
  · unfold Graph.FiniteObject.ambientSurplus
    exact Finset.sum_eq_zero fun vertex member => by rw [coreDegree vertex member]; simp
  · rw [Finset.disjoint_left]
    intro vertex inCore inCentres
    rw [centresEq, Finset.mem_singleton] at inCentres
    subst inCentres
    have := coreDegree _ inCore
    omega
  · refine ⟨split.separator, centresEq, ?_⟩
    rw [centresEq]
    unfold Graph.FiniteObject.ambientSurplus
    rw [Finset.sum_singleton]
  · rw [centresEq]
    unfold Graph.FiniteObject.ambientSurplus
    rw [Finset.sum_singleton]
    omega

/-- A vertex of a support has at most `|support| - 1` neighbours inside it. -/
theorem internalDegree_le_card_sub_one (support : Finset object.Vertex)
    {vertex : object.Vertex} (member : vertex ∈ support) :
    object.internalDegree support vertex ≤ support.card - 1 := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  unfold Graph.FiniteObject.internalDegree
  calc _ ≤ (support.erase vertex).card := by
        apply Finset.card_le_card
        intro other hother
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hother
        exact Finset.mem_erase.mpr ⟨(object.graph.ne_of_adj hother.1).symm, hother.2⟩
    _ = support.card - 1 := Finset.card_erase_of_mem member

theorem pairHandoffNetCharge_holds
    (handoff : ∃ returns, canonicalPairDemandReturns data object = some returns ∧
      PairObstructionHandoff data object returns) :
    PairHandoffNetChargeStatement data object := by
  classical
  obtain ⟨returns, returnsSelected, routes, split, core, centres, hsep, supportSelected,
    coreEq, centresEq, _nonempty, high, _coreInU, _centresInU⟩ :=
    pairHandoffSupport_holds handoff
  have coreCard : 1 ≤ core.card ∧ core.card ≤ 2 := by
    rw [coreEq]
    unfold pairObstructionCore
    letI : DecidableEq object.Vertex := object.vertices.decEq
    exact ⟨Finset.card_pos.mpr ⟨_, Finset.mem_insert_self _ _⟩, Finset.card_le_two⟩
  have lower : (data.threshold - 1) * core.card ≤
      object.positiveDeficiency core data.threshold := by
    unfold Graph.FiniteObject.positiveDeficiency
    calc (data.threshold - 1) * core.card
        = ∑ _vertex ∈ core, (data.threshold - 1) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun vertex member => by
        have := internalDegree_le_card_sub_one (object := object) core member
        omega
  have upper : object.positiveDeficiency core data.threshold ≤
      data.threshold * core.card := by
    unfold Graph.FiniteObject.positiveDeficiency
    calc _ ≤ ∑ _vertex ∈ core, data.threshold :=
          Finset.sum_le_sum fun vertex _ => Nat.sub_le _ _
      _ = data.threshold * core.card := by simp [mul_comm]
  refine ⟨returns, returnsSelected, core, centres, supportSelected, coreCard.1, coreCard.2,
    lower, upper, ?_⟩
  intro envelope henv
  obtain ⟨shapeCore, shapeDec⟩ := pairObstructionEnvelope_shape hsep henv
  have ec : envelope.core = core := shapeCore.trans coreEq.symm
  have ed : envelope.decorations = centres := shapeDec.trans centresEq.symm
  by_cases negative : envelope.NegativeCharge data.threshold data.dischargeScale
  · exact Or.inl negative
  · right
    unfold Graph.DecoratedHandoff.Envelope.NegativeCharge
      Graph.DecoratedHandoff.Envelope.centreTokens at negative
    rw [ec, ed] at negative
    push Not at negative
    have below : object.ambientSurplus centres data.threshold <
        object.positiveDeficiency core data.threshold := by
      by_contra notBelow
      have := Nat.mul_le_mul_left data.dischargeScale (not_lt.mp notBelow)
      omega
    have centreHigh : data.threshold < object.degree split.separator :=
      high split.separator (by rw [centresEq]; exact Finset.mem_singleton_self _)
    refine ⟨below, split.separator, centresEq, ?_⟩
    have surplus : object.ambientSurplus centres data.threshold =
        object.degree split.separator - data.threshold := by
      rw [centresEq]
      unfold Graph.FiniteObject.ambientSurplus
      rw [Finset.sum_singleton]
    have bound := Nat.mul_le_mul_left data.threshold coreCard.2
    omega

end Hypostructure.Graph.Contracts.Spine.PairHandoffSupport
