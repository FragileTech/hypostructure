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

theorem pairHandoffFlowCut_holds
    (support : PairHandoffSupportStatement data object)
    (free : ExtFreeEmptyStatement data object)
    (overloadedStatement : ExtOverloadedTokenStatement data object) :
    PairHandoffFlowCutStatement data object := by
  classical
  obtain ⟨returns, returnsSelected, -⟩ := support
  obtain ⟨c, hc, hfree⟩ := free
  obtain ⟨c', hc', hover⟩ := overloadedStatement
  have same : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst same
  refine ⟨returns, returnsSelected, c', hc', ?_, ?_⟩
  · intro pair member
    have scheduled := returns.overlap.system.first.pairSet_subset_schedule member
    cases charge : extCharge data.LengthOK c' pair with
    | none =>
        exfalso
        have inFree : pair ∈ extFree data.LengthOK c' :=
          Finset.mem_filter.2 ⟨scheduled, charge⟩
        rw [hfree] at inFree
        simp at inFree
    | some token =>
        exact ⟨token, extCharge_mem_tokens data.LengthOK c' scheduled charge, rfl⟩
  · intro positive
    obtain ⟨overloaded, overloadedMem, overloadedLoad⟩ := hover positive
    obtain ⟨token, selected, tokenMem, tokenLoad⟩ :=
      canonicalChoice_spec
        (spec := fun t => t ∈ c'.tokens ∧
          homogeneousTokenCap data.routingLabelBound < extLoad data.LengthOK c' t)
        ⟨overloaded, overloadedMem, overloadedLoad⟩
    exact ⟨token, selected, tokenMem, tokenLoad, rfl⟩

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

/-- The level bound turns the failure of doubling into a level where it fails. -/
theorem exists_deficient_level (count : Nat → Nat) (total : Nat)
    (step : ∀ level, level < total → count (level + 1) ≤ 2 * count level)
    (deficient : count total ≠ 2 ^ total * count 0) :
    ∃ level, level < total ∧ count (level + 1) < 2 * count level := by
  by_contra none
  push Not at none
  have equal : ∀ level, level ≤ total → count level = 2 ^ level * count 0 := by
    intro level
    induction level with
    | zero => intro _; simp
    | succ level ih =>
        intro bound
        have h1 := step level (by omega)
        have h2 := none level (by omega)
        have h3 := ih (by omega)
        rw [pow_succ]
        calc count (level + 1) = 2 * count level := le_antisymm h1 h2
          _ = 2 ^ level * 2 * count 0 := by rw [h3]; ring
  exact deficient (equal total le_rfl)

theorem pairObstructionCountDeficit_holds
    (support : PairHandoffSupportStatement data object) :
    PairObstructionCountDeficitStatement data object := by
  classical
  obtain ⟨returns, returnsSelected, -⟩ := support
  refine ⟨returns, returnsSelected, fun order => ?_⟩
  have notRealizing : ¬ returns.overlap.system.toSkeletonModel.RealizingOrder
      (LengthOK := data.LengthOK) returns.overlap.family :=
    returns.overlap.minimal.1.2
  let count : Nat → Nat := fun level =>
    if bound : level ≤ returns.overlap.family.card then
      returns.overlap.system.toSkeletonModel.signatureCount (LengthOK := data.LengthOK)
        returns.overlap.family order level bound
    else 0
  have deficient : count returns.overlap.family.card ≠
      2 ^ returns.overlap.family.card * count 0 := by
    intro equal
    apply notRealizing
    refine ⟨order, ?_⟩
    have zeroBound : 0 ≤ returns.overlap.family.card := Nat.zero_le _
    simp only [count, dif_pos zeroBound, dif_pos (le_refl returns.overlap.family.card)] at equal
    exact equal
  obtain ⟨level, below, lt⟩ := exists_deficient_level count returns.overlap.family.card
    (fun level bound => by
      have bound' : level + 1 ≤ returns.overlap.family.card := bound
      have := returns.overlap.system.toSkeletonModel.signatureCount_succ_le
        (LengthOK := data.LengthOK)
        returns.overlap.family order level bound'
      simpa [count, bound', Nat.le_of_succ_le bound'] using this)
    deficient
  have bound' : level + 1 ≤ returns.overlap.family.card := below
  refine ⟨level, bound', ?_⟩
  simpa [count, bound', Nat.le_of_succ_le bound'] using lt

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
