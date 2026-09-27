import Hypostructure.Graph.Contracts.RouteEight.Basic
import Hypostructure.Graph.Contracts.TypeA.Support

/-!
# Contracts: node `[123]`, the exact large-budget descent

`thm:large-budget-route8-only` on the unified census: the deterministic
exit-`(4)` peeling procedure terminates at a recorded stage with exact stage
accounting (`route8PeelingDescent`), and when that terminal stage passes the
reduced-rate test it carries a true two-support route-`8` entry, the input of
node `[124]` (`route8StageTrueEntry`).
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **`thm:large-budget-route8-only`, the procedure**, with
`lem:typeA-peeling-stage-accounting`, `lem:typeA-peeling-reduced-reduction`,
`lem:typeA-pressure-is-exit4-peel` and `lem:typeA-exit4-finite-descent`: the
deterministic procedure `route8DescentStep` (lexicographically first
two-support entry, peeled when target-defect) is run from the empty peeling;
every stage carries the exact reduced/peeled accounting, every peel is fresh,
so after `|\tilde\Xi|` steps it has stopped, at a stage that either fails the
reduced-rate test or passes it with a true two-support entry. -/
theorem route8DescentChain_stageOutcome (data : Parameters)
    (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree)
    (thresholdPos : 1 ≤ data.threshold)
    (dischargePos : 1 ≤ data.dischargeScale)
    (normalized : RemainderNormalizedStatement data object)
    (deficit : Route8UnifiedDeficitFact data object) :
    Route8Pressure.StageOutcome object (canonicalWindowPacking data object)
      (route8UnifiedEntries data object) (route8UnifiedComponents data object)
      data.threshold data.dischargeScale (route8StageSlack data object)
      data.LengthOK (route8DescentChain data object) := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let components := route8UnifiedComponents data object
  let entries := route8UnifiedEntries data object
  let scaledDeficit := TypeBEnvelopeCharge.route8Deficit object support
    data.threshold data.dischargeScale components
  let slack := route8StageSlack data object
  have degreeBaseline : ∀ vertex : object.Vertex,
      data.threshold ≤ object.degree vertex :=
    degree_ge_of_minDegree data object baseline
  obtain ⟨valid, -, maximal⟩ := canonicalWindowPacking_spec data object
  have componentsSub : components ⊆ object.canonicalPieces support :=
    Finset.filter_subset _ _
  have surplusZero : ∀ component ∈ components,
      object.ambientSurplus (object.pieceSupport support component)
        data.threshold = 0 := fun component componentMem =>
    ((Finset.mem_filter.1 componentMem).2).1
  have routedFact : ∀ piece : Finset object.Vertex,
      piece ⊆ support →
      object.ambientSurplus piece data.threshold = 0 →
      ∀ vertex ∈ piece,
        object.internalDegree piece vertex = data.threshold →
        ∃ receiver : object.Vertex,
          object.traceReceiver? piece data.threshold vertex = some receiver ∧
            object.IsReceiver piece data.threshold receiver :=
    fun piece sub zero =>
      (Contracts.TypeA.zeroSurplusRoutingAt_of_normalized data object normalized
        sub zero).1
  have entriesSubset : entries ⊆
      Route8Census.entries object packing data.threshold data.dischargeScale :=
    route8UnifiedEntries_subset_entries data object
  have unifiedDeficit : support.card ≤
      scaledDeficit + data.dischargeScale *
          (Route8Census.supply object packing).card + slack := by
    have strong : support.card ≤
        scaledDeficit + data.dischargeScale *
            (Route8Census.supply object packing).card +
          data.bridgeMassFactor * data.dischargeScale *
            data.surplusThreshold object.vertexCount := by
      simpa [Route8UnifiedDeficitFact, support, components, scaledDeficit]
        using deficit
    simp only [slack, route8StageSlack]
    omega
  have accountingOf : ∀ chain : List (Route8Census.Index object),
      Route8Pressure.PeelChain object packing entries data.threshold
          data.dischargeScale slack data.LengthOK chain →
        chain.toFinset ⊆ entries →
        Route8Pressure.StageAccounting object packing entries components
            data.threshold data.dischargeScale slack chain ∧
          support.card ≤
            (Route8Pressure.peeledEntries object entries chain.toFinset).card +
              chain.toFinset.card +
              data.dischargeScale * (Route8Census.supply object packing).card +
              slack := by
    intro chain valid' chainSub
    -- The stage-local four-class accounting is independent of the rate test;
    -- in particular it remains available on the failed arm routed to `[181]`.
    have burden := Route8Pressure.stage_burden object packing components
      data.threshold data.dischargeScale dischargePos degreeBaseline
      componentsSub surplusZero routedFact chain.toFinset
    have burden' : scaledDeficit ≤
        (Route8Pressure.peeledEntries object entries chain.toFinset).card +
          chain.toFinset.card := by
      simpa [scaledDeficit, support, entries, route8UnifiedEntries] using burden
    have stageDeficit : support.card ≤
        (Route8Pressure.peeledEntries object entries chain.toFinset).card +
          chain.toFinset.card +
          data.dischargeScale * (Route8Census.supply object packing).card +
          slack := by
      omega
    have partition : entries =
        Route8Pressure.peeledEntries object entries chain.toFinset ∪
          chain.toFinset := by
      ext index
      simp only [Route8Pressure.peeledEntries, Finset.mem_union,
        Finset.mem_sdiff]
      constructor
      · intro indexMem
        by_cases peeledMem : index ∈ chain.toFinset
        · exact Or.inr peeledMem
        · exact Or.inl ⟨indexMem, peeledMem⟩
      · rintro (⟨indexMem, _⟩ | peeledMem)
        · exact indexMem
        · exact chainSub peeledMem
    have reducedDisjoint : Disjoint
        (Route8Pressure.peeledEntries object entries chain.toFinset)
        chain.toFinset := by
      rw [Finset.disjoint_left]
      intro index reducedMem peeledMem
      exact (Finset.mem_sdiff.1 reducedMem).2 peeledMem
    have peeledLeDeficit : chain.toFinset.card ≤ scaledDeficit := by
      induction valid' with
      | nil => simp
      | @cons previousChain index previous previousRate member _ _ ih =>
          have fresh : index ∉ previousChain.toFinset :=
            (Finset.mem_sdiff.1 member).2
          have rateRaw :
              (data.threshold * data.dischargeScale + 1) *
                  (Route8Census.supply object packing).card +
                  data.threshold * slack +
                  data.threshold * previousChain.toFinset.card <
                data.threshold * support.card := by
            simpa only [Route8Pressure.StageRate, support] using previousRate
          have scaledBudget := Nat.mul_le_mul_left data.threshold unifiedDeficit
          simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc] at scaledBudget
          simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc] at rateRaw
          have scaledPeel :
              data.threshold * previousChain.toFinset.card <
                data.threshold * scaledDeficit := by
            omega
          have previousLt : previousChain.toFinset.card < scaledDeficit :=
            Nat.lt_of_mul_lt_mul_left scaledPeel
          rw [List.toFinset_cons, Finset.card_insert_of_notMem fresh]
          omega
    have exactReduced : scaledDeficit =
        scaledDeficit - chain.toFinset.card + chain.toFinset.card :=
      (Nat.sub_add_cancel peeledLeDeficit).symm
    have reducedBurden : scaledDeficit - chain.toFinset.card ≤
        (Route8Pressure.peeledEntries object entries chain.toFinset).card := by
      omega
    have accounting : Route8Pressure.StageAccounting object packing entries
        components data.threshold data.dischargeScale slack chain :=
      ⟨chainSub, partition, reducedDisjoint, peeledLeDeficit, exactReduced,
        burden', reducedBurden, stageDeficit⟩
    exact ⟨accounting, stageDeficit⟩
  -- One stage of the deterministic procedure either stops or peels one fresh
  -- target-defect two-support entry of the current ledger.
  have stepSpec : ∀ chain : List (Route8Census.Index object),
      Route8Pressure.PeelChain object packing entries data.threshold
          data.dischargeScale slack data.LengthOK chain →
        route8DescentStep data object chain = chain ∨
          ∃ index, route8DescentStep data object chain = index :: chain ∧
            index ∈ Route8Pressure.peeledEntries object entries chain.toFinset ∧
            Route8Pressure.PeelChain object packing entries data.threshold
              data.dischargeScale slack data.LengthOK (index :: chain) := by
    intro chain valid'
    unfold route8DescentStep
    by_cases rate : Route8Pressure.StageRate object packing data.threshold
        data.dischargeScale slack chain.toFinset
    · simp only [packing, slack] at rate
      rw [if_pos rate]
      rcases hpick : route8LexFirst object
          ((Route8Pressure.peeledEntries object (route8UnifiedEntries data object)
            chain.toFinset).filter fun index =>
            Route8Pressure.TwoCarrierAt object (canonicalWindowPacking data object)
              (route8UnifiedEntries data object) data.threshold data.LengthOK
              chain.toFinset index) with _ | index
      · exact Or.inl rfl
      · have picked := (Finset.mem_filter.mp (route8LexFirst_spec hpick).1)
        by_cases defect : Route8Pressure.TargetDefectAt object data.threshold
            data.dischargeScale (HasCycleWithLength data.LengthOK) chain.toFinset
            index
        · refine Or.inr ⟨index, by simp only [if_pos defect], picked.1, ?_⟩
          exact Route8Pressure.PeelChain.cons valid' rate picked.1 picked.2 defect
        · exact Or.inl (by simp only [if_neg defect])
    · simp only [packing, slack] at rate
      rw [if_neg rate]
      exact Or.inl rfl
  let stage := fun k : Nat => (route8DescentStep data object)^[k] []
  have invariant : ∀ k : Nat,
      Route8Pressure.PeelChain object packing entries data.threshold
          data.dischargeScale slack data.LengthOK (stage k) ∧
        (stage k).toFinset ⊆ entries ∧
        ((stage k).toFinset.card = k ∨
          route8DescentStep data object (stage k) = stage k) := by
    intro k
    induction k with
    | zero => exact ⟨Route8Pressure.PeelChain.nil, by simp [stage], Or.inl (by simp [stage])⟩
    | succ k ih =>
        obtain ⟨valid', sub, count⟩ := ih
        have succEq : stage (k + 1) = route8DescentStep data object (stage k) :=
          Function.iterate_succ_apply' _ _ _
        rcases stepSpec (stage k) valid' with fixed | ⟨index, stepEq, member, valid''⟩
        · rw [succEq, fixed]
          exact ⟨valid', sub, Or.inr fixed⟩
        · have fresh : index ∉ (stage k).toFinset := (Finset.mem_sdiff.1 member).2
          have idxAll : index ∈ entries :=
            Route8Pressure.peeledEntries_subset object entries _ member
          rw [succEq, stepEq]
          refine ⟨valid'', ?_, ?_⟩
          · rw [List.toFinset_cons]
            exact Finset.insert_subset idxAll sub
          · rcases count with card | fixed
            · left
              rw [List.toFinset_cons, Finset.card_insert_of_notMem fresh, card]
            · exact absurd (stepEq.symm.trans fixed) (List.cons_ne_self _ _)
  let final := stage entries.card
  obtain ⟨valid', sub, count⟩ := invariant entries.card
  have fixed : route8DescentStep data object final = final := by
    rcases count with card | fixed
    · rcases stepSpec final valid' with fixed | ⟨index, _, member, _⟩
      · exact fixed
      · have full : final.toFinset = entries :=
          Finset.eq_of_subset_of_card_le sub (by rw [card])
        have empty : Route8Pressure.peeledEntries object entries final.toFinset = ∅ := by
          simp [Route8Pressure.peeledEntries, full]
        rw [empty] at member
        exact absurd member (Finset.notMem_empty _)
    · exact fixed
  obtain ⟨accounting, stageDeficit⟩ := accountingOf final valid' sub
  have finalEq : route8DescentChain data object = final := rfl
  rw [finalEq]
  refine ⟨valid', accounting, ?_⟩
  by_cases rate : Route8Pressure.StageRate object packing data.threshold
      data.dischargeScale slack final.toFinset
  · obtain ⟨index₀, member₀, two₀⟩ :=
      Route8Pressure.exists_twoCarrierEntry_staged object packing entries
        data.threshold data.dischargeScale slack data.LengthOK thresholdPos
        entriesSubset final.toFinset stageDeficit rate
    obtain ⟨index, hpick⟩ := route8LexFirst_isSome (object := object)
      (family := (Route8Pressure.peeledEntries object entries final.toFinset).filter
        fun index => Route8Pressure.TwoCarrierAt object packing entries
          data.threshold data.LengthOK final.toFinset index)
      ⟨index₀, Finset.mem_filter.mpr ⟨member₀, two₀⟩⟩
    have picked := Finset.mem_filter.mp (route8LexFirst_spec hpick).1
    have notDefect : ¬ Route8Pressure.TargetDefectAt object data.threshold
        data.dischargeScale (HasCycleWithLength data.LengthOK) final.toFinset
        index := by
      intro defect
      have stepEq : route8DescentStep data object final = index :: final := by
        unfold route8DescentStep
        simp only [packing, slack] at rate
        rw [if_pos rate]
        simp only [packing, entries] at hpick
        rw [hpick]
        simp only [if_pos defect]
      exact List.cons_ne_self _ _ (stepEq.symm.trans fixed)
    exact Or.inl ⟨rate, index, picked.1, picked.2, notDefect⟩
  · exact Or.inr rate

/-- **Node `[123]`, the descent fact**: the terminal stage
`route8DescentChain` of the procedure is a recorded peel chain with exact stage
accounting, and it either passes the reduced-rate test with a true two-support
entry or fails that test. -/
theorem route8PeelingDescent (data : Parameters) (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree)
    (thresholdPos : 1 ≤ data.threshold)
    (dischargePos : 1 ≤ data.dischargeScale)
    (normalized : RemainderNormalizedStatement data object)
    (deficit : Route8UnifiedDeficitFact data object) :
    Route8PeelingDescentStatement data object :=
  route8DescentChain_stageOutcome data object baseline thresholdPos dischargePos
    normalized deficit

/-- **`thm:large-budget-route8-only`, the true entry of a stage**: a true
entry of the terminal stage is not target-defective at that stage, so by the
unified census (`lem:typeA-unified-carriers`) its basin is
target-complete-minimal and its load has no exit-`(4)` witness. -/
theorem stageTrueEntry_at (data : Parameters) (object : FiniteObject.{u})
    (census : Route8UnifiedEntryCensusFact data object)
    {index : Route8Census.Index object}
    (isTrue : Route8StageTrueEntrySpec data object index) :
    Route8TerminalTrueEntry data object index := by
  classical
  letI : DecidableEq object.Vertex := Route8.vertexDecEq object
  let final := route8DescentChain data object
  have transported := Route8Pressure.trueEntry_transport object
    (canonicalWindowPacking data object) (route8UnifiedEntries data object)
    data.threshold data.dischargeScale data.LengthOK final.toFinset isTrue
  have entryFacts := census index transported.1
  rcases entryFacts.2.2 with routeEntry | targetDefect
  · exact ⟨transported.1, transported.2.1, entryFacts, routeEntry,
      transported.2.2⟩
  · obtain ⟨witness, witnessLoad⟩ := targetDefect.2.2.2.2
    have fresh : index ∉ final.toFinset := (Finset.mem_sdiff.mp isTrue.1).2
    have currentDefect := Route8Pressure.targetDefectAt_of_empty object
      data.threshold data.dischargeScale (HasCycleWithLength data.LengthOK)
      final.toFinset index fresh witness witnessLoad
    exact (isTrue.2.2 currentDefect).elim

/-- **Node `[123]`, yes arm → node `[334]`**: on the rate arm the terminal
entry `ξ` is the true entry `ξ†` of the terminal stage of `route8DescentChain`,
and it is a true two-support route-`8` entry. -/
theorem route8StageTrueEntry (data : Parameters) (object : FiniteObject.{u})
    (descent : Route8PeelingDescentStatement data object)
    (rate : Route8StageRateStatement data object)
    (census : Route8UnifiedEntryCensusFact data object) :
    Route8UnifiedTrueTwoCarrierEntryStatement data object := by
  obtain ⟨_chain, _accounting, ends⟩ := descent
  have exists_ : ∃ index, Route8StageTrueEntrySpec data object index := by
    rcases ends with ⟨_rate, index, isTrue⟩ | rateFails
    · exact ⟨index, isTrue⟩
    · exact (rateFails rate).elim
  obtain ⟨index, pin, isTrue⟩ :=
    canonicalRoute8StageTrueEntry_spec data object exists_
  refine ⟨index, ?_, stageTrueEntry_at data object census isTrue⟩
  rw [canonicalRoute8TerminalEntry_eq_of_rate data object rate]
  exact pin

end Hypostructure.Graph.Contracts.RouteEight
