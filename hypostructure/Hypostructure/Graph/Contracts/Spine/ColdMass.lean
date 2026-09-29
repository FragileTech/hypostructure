import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Contracts.Spine.ColdFirstFailure

/-!
# Contracts: the cold mass `[149]`--`[153]`, `[162]`, `[24]`, `[176]`

Proof-agnostic contract lemmas for `lem:hot-failure-cold-mass`, the ambient
cubic charge, the branch-excess count, the strict positivity of the germ
family, the dense cold pass, the window-only density cap, and the closure of
the cold branch.  Each lemma is stated over a `Graph.FiniteObject` with the
registered `Parameters` as a parameter and every paper hypothesis explicit; its
conclusion is exactly the statement of the fact it proves.  This module
imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[150]`, `lem:hot-failure-cold-mass`.**  The hot windows of the
fixed packing fit the skeleton allowance at the window bit rate, so the packing
count splits as hot plus cold and the cleared cold-mass inequality holds. -/
theorem coldMass_of_hotCap (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (split : HotColdWindowStatement data object)
    (hotBound : ColdHotEntropyCapStatement data object) :
    ColdMassStatement data object := by
  classical
  let packing := canonicalWindowPacking data object
  let hot := canonicalHotWindows data object
  let cold := canonicalColdWindows data object
  change coldWindowBitRate data object * hot.card ≤
    coldSkeletonAllowance data object at hotBound
  have hotSubset : hot ⊆ packing := by
    rcases split with ⟨_, _, _, hotFacts, _, _, _⟩
    exact hotFacts.1
  have count : packing.card = hot.card + cold.card := by
    have := (Finset.card_sdiff_add_card_eq_card hotSubset).symm
    rw [Nat.add_comm] at this
    exact this
  change ColdMassStatement data object
  simpa [ColdMassStatement] using
    Graph.ColdCorridor.hotFailure_coldMass
      (coldWindowBitRate data object) 0 0
      (coldSkeletonAllowance data object)
      hot.card cold.card packing.card count (by simpa using hotBound)

/-- **Node `[151]`, the ambient-cubic charge.**  Each non-ambient-cubic cold
window of the fixed packing contains a vertex above the baseline; the windows
are disjoint, so these vertices are distinct and are counted by the degree
surplus. -/
theorem coldAmbientCubic_of_split (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (split : HotColdWindowStatement data object)
    (nearCubic : SurplusAtOrBelowStatement data object) :
    ColdAmbientCubicStatement data object := by
  classical
  rcases split with
    ⟨valid, _attains, _maximal, _hotIff, coldIff, _disjoint, _cover⟩
  have coldSubset : canonicalColdWindows data object ⊆
      canonicalWindowPacking data object := by
    intro window member
    exact (coldIff window).mp member |>.1
  change ColdAmbientCubicStatement data object
  refine ⟨?_, nearCubic⟩
  let packing := canonicalWindowPacking data object
  let cold := canonicalColdWindows data object
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := inferInstance
  let ambient : Finset object.Vertex := Finset.univ.filter fun vertex =>
    data.threshold < object.degree vertex
  let bad : Finset (Finset object.Vertex) := cold.filter fun window =>
    ¬ AmbientCubicWindow data object window
  have baselineDegree : ∀ vertex : object.Vertex,
      data.threshold ≤ object.degree vertex := fun vertex =>
    le_trans baseline (object.minDegree_le_degree vertex)
  have existsHigh (window : {window // window ∈ bad}) :
      ∃ vertex ∈ window.1, data.threshold < object.degree vertex := by
    have notCubic := (Finset.mem_filter.mp window.property).2
    simp only [AmbientCubicWindow] at notCubic
    push Not at notCubic
    obtain ⟨vertex, member, different⟩ := notCubic
    have lower := baselineDegree vertex
    exact ⟨vertex, member, by omega⟩
  let chosen : {window // window ∈ bad} → {vertex // vertex ∈ ambient} :=
    fun window => ⟨Classical.choose (existsHigh window),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Classical.choose_spec (existsHigh window)).2⟩⟩
  have chosenMem (window : {window // window ∈ bad}) :
      (chosen window).1 ∈ window.1 :=
    (Classical.choose_spec (existsHigh window)).1
  have chosenInjective : Function.Injective chosen := by
    intro left right same
    apply Subtype.ext
    by_contra different
    have leftPacking : left.1 ∈ packing :=
      coldSubset (Finset.mem_filter.mp left.property).1
    have rightPacking : right.1 ∈ packing :=
      coldSubset (Finset.mem_filter.mp right.property).1
    have disjoint := valid.2 left.1 leftPacking right.1 rightPacking different
    have sameVertex : (chosen left).1 = (chosen right).1 :=
      congrArg Subtype.val same
    exact (Finset.disjoint_left.mp disjoint)
      (chosenMem left) (sameVertex.symm ▸ chosenMem right)
  have badCard : bad.card ≤ ambient.card := by
    simpa using Fintype.card_le_of_injective chosen chosenInjective
  have ambientCard : ambient.card ≤ object.degreeSurplus data.threshold := by
    calc
      ambient.card = ∑ _vertex ∈ ambient, 1 := by simp
      _ ≤ ∑ vertex ∈ ambient,
            (object.degree vertex - data.threshold) := by
        exact Finset.sum_le_sum fun vertex member => by
          have high := (Finset.mem_filter.mp member).2
          omega
      _ ≤ ∑ vertex ∈ (Finset.univ : Finset object.Vertex),
            (object.degree vertex - data.threshold) := by
        exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = object.degreeSurplus data.threshold := by
        simpa [Graph.FiniteObject.ambientSurplus] using
          object.ambientSurplus_univ_eq_degreeSurplus
            data.threshold baselineDegree
  have badBound : bad.card ≤ object.degreeSurplus data.threshold :=
    badCard.trans ambientCard
  have splitCard := cold.card_filter_add_card_filter_not
    (AmbientCubicWindow data object)
  change cold.card ≤
    (cold.filter (AmbientCubicWindow data object)).card +
      object.degreeSurplus data.threshold
  rw [← splitCard]
  convert Nat.add_le_add_left badBound
    (cold.filter (AmbientCubicWindow data object)).card using 1

/-- **Node `[152]`, the exact external stub count** of every ambient-cubic
cold window of the fixed packing. -/
theorem coldAmbientCubicStubExcess_of_split (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (split : HotColdWindowStatement data object) :
    ColdAmbientCubicStubExcessStatement data object := by
  classical
  let packing := canonicalWindowPacking data object
  rcases split with
    ⟨valid, _attains, _maximal, _hotFacts, coldIff, _hotCold, _cover⟩
  intro window member
  have packingMem : window ∈ packing :=
    (coldIff window).mp (Finset.mem_filter.mp member).1 |>.1
  have stubCount :=
    Graph.ColdCorridor.externalStubList_length_add_internal_eq_stubCount
      object window (valid.1 window packingMem)
        (Finset.mem_filter.mp member).2
  simpa only [coldExternalStubCount] using
    Nat.eq_sub_of_add_eq stubCount

/-- **Node `[152]`, the selected branch excess.**  On the cubic baseline every
ambient-cubic window of order `windowOrder ≥ 3` has exactly two end vertices,
so it selects `windowOrder - 2` interior stubs; the windows are disjoint, so
the selected stubs are counted window by window and each has a unique window. -/
theorem coldSelectedBranchExcess_of_split (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (thresholdEq : data.threshold = 3)
    (threeLeOrder : 3 ≤ data.windowOrder)
    (split : HotColdWindowStatement data object) :
    ColdSelectedBranchExcessStatement data object := by
  classical
  let packing := canonicalWindowPacking data object
  let cold := canonicalColdWindows data object
  let cubicWindows := cold.filter (AmbientCubicWindow data object)
  rcases split with
    ⟨valid, _attains, _maximal, _hotFacts, coldIff, _hotCold, _cover⟩
  have cubicSubset : cubicWindows ⊆ packing := by
    intro window member
    exact (coldIff window).mp (Finset.mem_filter.mp member).1 |>.1
  have cubicDisjoint : ∀ left ∈ cubicWindows, ∀ right ∈ cubicWindows,
      left ≠ right → Disjoint left right := by
    intro left leftMem right rightMem different
    exact valid.2 left (cubicSubset leftMem) right (cubicSubset rightMem) different
  change ColdSelectedBranchExcessStatement data object
  refine ⟨?_, ?_⟩
  · rw [Graph.ColdCorridor.card_allSelectedStubs object cubicWindows
        cubicDisjoint]
    calc
      ∑ window ∈ cubicWindows,
            ((Graph.ColdCorridor.interiorStubList object window).length - 2) =
          ∑ _window ∈ cubicWindows,
            coldInteriorBranchExcess data := by
        refine Finset.sum_congr rfl fun window member => ?_
        have packingMem : window ∈ packing :=
          (coldIff window).mp (Finset.mem_filter.mp member).1 |>.1
        have induces : object.InducesWindow data.windowOrder window :=
          valid.1 window packingMem
        have cubicDegree : ∀ vertex ∈ window,
            object.degree vertex = data.threshold :=
          (Finset.mem_filter.mp member).2
        obtain ⟨ends, endsSubset, endsCard, interior, endpoints⟩ :=
          Graph.FiniteObject.exists_ends_externalNeighbours window
            threeLeOrder induces cubicDegree
        have interiorVertices : window.filter (fun vertex =>
            (object.externalNeighbours window vertex).card = 1) =
            window \ ends := by
          ext vertex
          simp only [Finset.mem_filter, Finset.mem_sdiff]
          constructor
          · rintro ⟨vertexMem, one⟩
            refine ⟨vertexMem, ?_⟩
            intro vertexEnd
            have count := endpoints vertex vertexEnd
            rw [thresholdEq] at count
            omega
          · rintro ⟨vertexMem, notEnd⟩
            refine ⟨vertexMem, ?_⟩
            have count := interior vertex vertexMem notEnd
            simpa [thresholdEq] using count
        have interiorLength :
            (Graph.ColdCorridor.interiorStubList object window).length =
              data.windowOrder - 2 := by
          rw [Graph.ColdCorridor.interiorStubList_length_eq_sum,
            interiorVertices]
          calc
            ∑ vertex ∈ window \ ends,
                  (object.externalNeighbours window vertex).card =
                ∑ _vertex ∈ window \ ends, 1 := by
              refine Finset.sum_congr rfl fun vertex vertexMem => ?_
              simpa [thresholdEq] using
                interior vertex (Finset.mem_sdiff.1 vertexMem).1
                  (Finset.mem_sdiff.1 vertexMem).2
            _ = (window \ ends).card := by simp
            _ = window.card - ends.card :=
              Finset.card_sdiff_of_subset endsSubset
            _ = data.windowOrder - 2 := by rw [induces.2, endsCard]
        rw [interiorLength]
        rfl
      _ = coldInteriorBranchExcess data * cubicWindows.card := by
        simp [Nat.mul_comm]
  · intro stub stubMem
    have represented : ∃ window ∈ cubicWindows,
        stub ∈ Graph.ColdCorridor.selectedStubs object window := by
      change stub ∈
        Graph.ColdCorridor.allSelectedStubs object cubicWindows at stubMem
      simpa only [Graph.ColdCorridor.allSelectedStubs,
        Finset.mem_biUnion] using stubMem
    obtain ⟨window, windowMem, stubInWindow⟩ := represented
    refine ⟨window, ⟨windowMem, stubInWindow⟩, ?_⟩
    intro other otherFacts
    rcases otherFacts with ⟨otherMem, stubInOther⟩
    by_contra different
    have disjoint := cubicDisjoint window windowMem other otherMem
      (Ne.symm different)
    exact Finset.disjoint_left.mp disjoint
      (Graph.ColdCorridor.mem_selectedStubs_isStub object stubInWindow).1
      (Graph.ColdCorridor.mem_selectedStubs_isStub object stubInOther).1

/-- **Node `[152]`, the branch-excess inequality** from the ambient-cubic
charge of `[151]`. -/
theorem coldStubExcess_of_ambientCubic (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (cubic : ColdAmbientCubicStatement data object) :
    ColdStubExcessStatement data object := by
  classical
  simpa [ColdStubExcessStatement, ColdAmbientCubicStatement] using
    Graph.ColdCorridor.branchExcess_ge_of_cubic
      (coldInteriorBranchExcess data)
      ((canonicalColdWindows data object).filter
        (AmbientCubicWindow data object)).card
      (canonicalColdWindows data object).card
      (object.degreeSurplus data.threshold) cubic.1

/-- **Node `[153]`, the bounded arm** is the exact complement of the linear
arm. -/
theorem coldMassBounded_of_not_linear (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (linear : ¬ ColdMassLinearStatement data object) :
    ColdMassBoundedStatement data object := by
  change ¬ ((coldInteriorBranchExcess data +
      (data.threshold + 1) *
        Graph.ColdCorridor.overlapBound data.threshold data.coldSignature) *
    object.degreeSurplus data.threshold <
      coldInteriorBranchExcess data *
        (canonicalColdWindows data object).card) at linear
  change coldInteriorBranchExcess data *
      (canonicalColdWindows data object).card ≤
    (coldInteriorBranchExcess data +
      (data.threshold + 1) *
        Graph.ColdCorridor.overlapBound data.threshold data.coldSignature) *
      object.degreeSurplus data.threshold
  exact Nat.le_of_not_lt linear

/-- **Node `[153]`, `lem:cold-germ-extraction`: strict positivity.**  On the
linear arm the selected `9C` mass exceeds the non-ambient-window loss plus the
first-high incidence loss, so the candidate family, and hence its greedy
disjoint subfamily, is nonempty. -/
theorem coldGermFamilyPositive_of_linear (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (family : ColdGermCandidatesStatement data object)
    (linear : ColdMassLinearStatement data object)
    (selectedExcess : ColdSelectedBranchExcessStatement data object)
    (stubExcess : ColdStubExcessStatement data object) :
    ColdGermFamilyPositiveStatement data object := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  let selected := Graph.ColdCorridor.allSelectedStubs object cubic
  let perWindow := coldInteriorBranchExcess data
  obtain ⟨⟨disjointFamily, corridorLoss⟩, extractionEq, routing,
      familyWitness⟩ := coldGermExtraction?_spec_of_candidates data object family
  simp only [ColdGermFamilyWitness] at familyWitness
  rcases familyWitness with
    ⟨_incidenceEq, _candidatesEq, _candidateFamily, extracted,
      _noncandidateClassified, _occurrenceCount, selectedCount,
      lossBound, _quantitative⟩
  set candidates := coldRoutedCandidates data object routing
  have lossSmall : corridorLoss < selected.card := by
    have selectedExact := selectedExcess.1
    change selected.card = perWindow * cubic.card at selectedExact
    change perWindow * cold.card ≤
      perWindow * cubic.card +
        perWindow * object.degreeSurplus data.threshold at stubExcess
    change (perWindow + (data.threshold + 1) *
        Graph.ColdCorridor.overlapBound data.threshold
          data.coldSignature) * object.degreeSurplus data.threshold <
      perWindow * cold.card at linear
    change corridorLoss ≤ (data.threshold + 1) *
        Graph.ColdCorridor.overlapBound data.threshold
          data.coldSignature * object.degreeSurplus data.threshold at lossBound
    rw [Nat.add_mul] at linear
    rw [selectedExact]
    omega
  have candidatePositive : 0 < candidates.card := by
    change selected.card = candidates.card + corridorLoss at selectedCount
    omega
  have disjointPositive : 0 < disjointFamily.card :=
    Graph.ColdCorridor.coldGerm_nonempty extracted.2.2 candidatePositive
  exact ⟨(disjointFamily, corridorLoss), extractionEq,
    disjointPositive⟩

/-- **Node `[162]`, `lem:dense-cold-pass`** (tex 7692-7694), on the
distinct-states arm: every retained cold return corridor of G is terminal in
the sense of the (F5) terminal subcase, or its first failure is a heavy handoff
centre.

The paper's reason for terminality ("the boundaried pieces of `R` are
induced-`P₁₃`-free and subcubic, [so] they have bounded diameter") does not reach
corridors of `G − X_cold`; the proof here is by G's first failures.  Each
retained corridor of G has a first failure (`K .coldFirstFailureOccurrence`).
(F1) is excluded by target avoidance and (F3) by uncompressibility, (F2) by
(★); the repeat subcase of (F5) carries two equal states up to the first
failure, excluded by (★) (`ColdCutStatesDistinctStatement`); the terminal
subcase of (F5) is terminal; an (F4) heavy centre is the disjunct
`ColdFirstFailureHandoffOccurrence`.  No terminality is asserted for a corridor
whose first failure is a heavy centre: nothing downstream reads it. -/
theorem denseColdCorridorsTerminal_of_distinct (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (occurrence : ColdFirstFailureOccurrenceStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (uncompressible : UncompressibleStatement data object)
    (distinct : ColdCutStatesDistinctStatement data object) :
    DenseColdCorridorsTerminalStatement data object := by
  classical
  let occurrenceData := Classical.choice occurrence
  refine ⟨occurrenceData, ?_⟩
  intro epsilon
  obtain ⟨first, event, minimal⟩ := occurrenceData.occurs epsilon
  cases event with
  | cycle cycle =>
      exact (coldFailureCycle_of_avoids data object avoids occurrenceData epsilon
        first cycle).elim
  | defect defect =>
      exact (coldFailureDefectRoutes_of_avoids data object avoids occurrenceData
        epsilon first defect).elim
  | compression compression =>
      exact (coldFailureCompression_of_uncompressible data object avoids
        uncompressible occurrenceData epsilon first compression).elim
  | handoff handoff =>
      exact Or.inr ⟨first, handoff, minimal⟩
  | germ germ =>
      rcases germ with ⟨terminal, _⟩ |
          ⟨left, right, _, lt, same, _, _, _, _, _, rightEq⟩
      · exact Or.inl terminal
      · subst rightEq
        exact (distinct occurrenceData epsilon first minimal left first lt le_rfl
          same).elim

/-- **Node `[162]`, the heavy entry is read within `Q_cold` states.**  On the
distinct-states arm the states up to the first failure are pairwise distinct, so
the first failure lies below `Q_cold` (`ColdEqualStates.first_lt_stateBound`). -/
theorem coldHeavyEntryTerminal_of_distinct (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (distinct : ColdCutStatesDistinctStatement data object) :
    ColdHeavyEntryTerminalStatement data object := by
  intro occurrence epsilon first minimal _handoff
  exact Graph.ColdEqualStates.first_lt_stateBound _ _ _ first
    (distinct occurrence epsilon first minimal)

/-- **`thm:cold-branch-quantitative-closure`: no terminal cold residual.**
With the germs extracted and routed and the same-interface table closed, no
local terminal cold pattern remains. -/
theorem coldBranchClosed_of_routing (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (routed : ColdGermRoutedStatement data object)
    (table : ColdSameInterfaceTableStatement data object) :
    ColdBranchClosedStatement data object := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨germ, active, shorter, _notDistinguishing⟩
    exact routed germ active shorter
  · rintro ⟨row, notHandoff, notDistinguishing⟩
    rcases (table.1 row).2 with handoff | distinguishing
    · exact notHandoff handoff
    · exact notDistinguishing distinguishing
  · rintro ⟨self, notHandoff, notDistinguishing⟩
    rcases (table.2.1 self).2.2 with handoff | distinguishing
    · exact notHandoff handoff
    · exact notDistinguishing distinguishing

/-- **Node `[24]`, `prop:p13-density` after the cold branch.**  On the bounded
arm the cold mass is `C ≤ (1 + (threshold+1)·B_cold)·σ(G)`; with the cleared
cold-mass inequality and the near-cubic surplus bound `σ(G) ≤ T(n)` this is the
window-only density cap with its exact `o(1)`. -/
theorem densityCapLinear_of_coldMassBounded (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (fiveLeOrder : 5 ≤ data.windowOrder)
    (mass : ColdMassStatement data object)
    (bounded : ColdMassBoundedStatement data object)
    (cubic : ColdAmbientCubicStatement data object)
    (split : HotColdWindowStatement data object) :
    2 * (data.windowRate * data.separatedScaleCount object.vertexCount *
        object.windowPackingNumber data.windowOrder) ≤
      (Graph.dyadicScaleCount object + 1) *
        (data.threshold * object.vertexCount +
          data.surplusThreshold object.vertexCount) +
      data.densitySlack * (data.windowRate * data.separatedScaleCount object.vertexCount) *
        data.surplusThreshold object.vertexCount := by
  classical
  let packing := canonicalWindowPacking data object
  let cold := canonicalColdWindows data object
  let perWindow := coldInteriorBranchExcess data
  have perWindowPos : 0 < perWindow := by
    have order := fiveLeOrder
    simp only [perWindow, coldInteriorBranchExcess,
      Graph.ColdCorridor.branchExcessOf]
    omega
  let overlap := Graph.ColdCorridor.overlapBound data.threshold data.coldSignature
  let highLoss := (data.threshold + 1) * overlap
  have coldBound : cold.card ≤
      (1 + highLoss) * object.degreeSurplus data.threshold := by
    change perWindow * cold.card ≤
      (perWindow + highLoss) * object.degreeSurplus data.threshold at bounded
    have : perWindow * cold.card ≤
        perWindow * ((1 + highLoss) * object.degreeSurplus data.threshold) := by
      refine bounded.trans ?_
      have : perWindow + highLoss ≤ perWindow * (1 + highLoss) := by
        have := Nat.mul_le_mul_right highLoss perWindowPos
        rw [Nat.mul_add]; omega
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ this
    exact Nat.le_of_mul_le_mul_left this perWindowPos
  have surplusBound : object.degreeSurplus data.threshold ≤
      data.surplusThreshold object.vertexCount := by
    change (cold.card ≤ (cold.filter (AmbientCubicWindow data object)).card +
      object.degreeSurplus data.threshold) ∧
      object.degreeSurplus data.threshold ≤
        data.surplusThreshold object.vertexCount at cubic
    exact cubic.2
  have packingCard : packing.card = object.windowPackingNumber data.windowOrder := by
    rcases split with ⟨_, attains, _, _, _, _, _⟩
    exact attains
  change coldWindowBitRate data object * packing.card ≤
    coldWindowBitRate data object * cold.card +
      coldSkeletonAllowance data object at mass
  change 2 * (data.windowRate * data.separatedScaleCount object.vertexCount *
      object.windowPackingNumber data.windowOrder) ≤
    (Graph.dyadicScaleCount object + 1) *
      (data.threshold * object.vertexCount +
        data.surplusThreshold object.vertexCount) +
    data.densitySlack * (data.windowRate * data.separatedScaleCount object.vertexCount) *
      data.surplusThreshold object.vertexCount
  rw [← packingCard]
  have coldTerm : 2 * (data.windowRate * data.separatedScaleCount object.vertexCount) *
      cold.card ≤
      data.densitySlack * (data.windowRate * data.separatedScaleCount object.vertexCount) *
        data.surplusThreshold object.vertexCount := by
    calc 2 * (data.windowRate * data.separatedScaleCount object.vertexCount) *
          cold.card
        ≤ 2 * (data.windowRate * data.separatedScaleCount object.vertexCount) *
            ((1 + highLoss) * data.surplusThreshold object.vertexCount) :=
          Nat.mul_le_mul_left _ (coldBound.trans
            (Nat.mul_le_mul_left (1 + highLoss) surplusBound))
      _ = data.densitySlack * (data.windowRate * data.separatedScaleCount object.vertexCount) *
            data.surplusThreshold object.vertexCount := by
          simp only [Parameters.densitySlack, highLoss, overlap]; ring
  simp only [coldWindowBitRate, coldSkeletonAllowance] at mass
  have key := le_trans mass (Nat.add_le_add_right coldTerm _)
  calc 2 * (data.windowRate * data.separatedScaleCount object.vertexCount *
        packing.card)
      = 2 * (data.windowRate * data.separatedScaleCount object.vertexCount) *
          packing.card := by ring
    _ ≤ data.densitySlack * (data.windowRate * data.separatedScaleCount object.vertexCount) *
          data.surplusThreshold object.vertexCount +
        (Graph.dyadicScaleCount object + 1) *
          (data.threshold * object.vertexCount +
            data.surplusThreshold object.vertexCount) := key
    _ = (Graph.dyadicScaleCount object + 1) *
          (data.threshold * object.vertexCount +
            data.surplusThreshold object.vertexCount) +
        data.densitySlack * (data.windowRate * data.separatedScaleCount object.vertexCount) *
          data.surplusThreshold object.vertexCount := by ring

/-- **Node `[24]`, `prop:p13-density`**: the window-only linear cap after the
cold branch, and the high-entropy clause (tex 8491-8495, 8530-8551): a joint
window/remainder comparison realized by a state map on G's labelled skeleton
class fits the skeleton budget, since such a map realizes at most
`|𝒢_{n,m}|` states (`lem:skeleton-dominates`).  Solving the cleared inequality
is `θ ≤ 0.01198542083… + o(1)`. -/
theorem densityCap_of_coldMassBounded (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (fiveLeOrder : 5 ≤ data.windowOrder)
    (mass : ColdMassStatement data object)
    (bounded : ColdMassBoundedStatement data object)
    (cubic : ColdAmbientCubicStatement data object)
    (split : HotColdWindowStatement data object) :
    DensityCapStatement data object := by
  exact densityCapLinear_of_coldMassBounded data object fiveLeOrder mass bounded
    cubic split

end Hypostructure.Graph.Contracts.Spine
