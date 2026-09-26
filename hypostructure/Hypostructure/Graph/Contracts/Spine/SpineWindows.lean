import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.Statements.SurplusPair

/-!
# Contracts: the window packing and its live-hot cap `[17]`--`[23]`

Proof-agnostic contract lemmas for the maximal induced-window packing, the
certified barrier enumeration, the separated window package, the canonical
hot/cold partition, the live-hot barrier cap, and the relabelling density cap.
Each lemma is stated over a `Graph.FiniteObject` with the registered
`Parameters` as a parameter and every hypothesis explicit; its conclusion is
exactly the statement of the fact it proves.  This module imports no strategy,
row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u v

/-- **Node `[17]`.**  An object carrying an induced window has a positive
packing number, and a vertex-disjoint family attaining it; attaining the
maximum forces maximality, since a window disjoint from every member could be
added. -/
theorem maximalPacking_of_windowPresent (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (present : Graph.HasInducedPath object data.windowOrder) :
    MaximalPackingStatement data object := by
  have carried : ∃ support : Finset object.Vertex,
      object.InducesWindow data.windowOrder support := by
    by_contra empty
    push Not at empty
    exact Graph.FiniteObject.inducedPathFree_of_forall_not_inducesWindow
      object empty present
  obtain ⟨support, window⟩ := carried
  exact ⟨object.windowPackingNumber_pos data.windowOrder_pos window,
    canonicalWindowPacking_spec data object⟩

/-- **Node `[21]`, `lem:curv-enum`.**  The registered certified barrier table's
stored safe and flat counts are the finite safe, curvature-positive, and flat
enumerations, with their exact logarithmic ratio. -/
theorem barrierEnumeration (data : Parameters) :
    BarrierEnumerationStatement data := by
  unfold BarrierEnumerationStatement
  let barrier := data.windowBarrier
  letI := barrier.indexFintype
  let row := data.curvatureBarrierRow
  let left := barrier.table.counts.leftLength row
  let right := barrier.table.counts.rightLength row
  let safe := barrier.table.counts.storedSafe row
  let flat := barrier.table.counts.storedFlat row
  let curvaturePositive := safe - flat
  refine ⟨safe, curvaturePositive, flat, rfl, rfl, rfl,
    barrier.table.storedSafe_eq row, ?_,
    barrier.table.storedFlat_eq row, rfl⟩
  change barrier.table.counts.storedSafe row -
      barrier.table.counts.storedFlat row =
    barrier.profile.obstructedCount left right
  rw [barrier.table.storedSafe_eq, barrier.table.storedFlat_eq]
  rfl

/-- **Node `[21]`, `lem:p13-window-package`.**  On a selected object with the
replacement exclusion, the multi-scale window package of the fixed maximum
packing `P₀` is separated: its coordinates are disjoint per window, each
window carries `windowPackageBits` coordinates, the registered per-scale rate is
dominated by the compounded floor, and every functional declared quotient of
the package (or of a baseline family extended by it) is label-injective. -/
theorem windowPackageSeparated_of_maximalPacking
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation}
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (windowRate_eq_barrier : data.windowRate = data.windowBarrier.binaryRateFloor)
    (replacementExclusion : ReplacementExclusionStatement data object)
    (selection : SelectionStatement BranchState Presentation presentation data object) :
    WindowPackageSeparatedStatement data object := by
  classical
  simp only [WindowPackageSeparatedStatement]
  let noReplacement := replacementExclusion
  let selected := selection
  let packing := canonicalWindowPacking data object
  let barrier := data.windowBarrier
  letI := barrier.indexFintype
  let scales := data.separatedScaleCount
    object.vertexCount
  let safe := Core.Finite.CertifiedTableAggregation.safeProduct
    barrier.table
  let flat := Core.Finite.CertifiedTableAggregation.flatProduct
    barrier.table
  let bits := windowPackageBits data object
  have bitsEq : bits = Nat.log2 ((safe ^ scales - 1) / flat ^ scales) := rfl
  -- `|ℐ_win| ≥ (c₁₃ − o(1)) log₂ n` per window: the registered rate,
  -- floored once per scale, is dominated by the compounded floor.
  have rateLe : data.windowRate * scales ≤ bits := by
    rw [bitsEq]
    have flatPos : 0 < flat := barrier.flatPositive
    have improves : flat ≤ safe := barrier.improves
    rcases Nat.eq_zero_or_pos scales with scalesZero | scalesPos
    · simp [scalesZero]
    rcases lt_or_eq_of_le improves with flatLt | flatEq
    · -- `2 ^ rate · flat ≤ safe − 1`, then compound across the scales.
      have rateBound : 2 ^ data.windowRate * flat ≤ safe - 1 := by
        have rateDef : data.windowRate =
            Nat.log2 ((safe - 1) / flat) := by
          rw [windowRate_eq_barrier]
          show Core.Finite.CertifiedTableAggregation.binaryRateFloor
            barrier.table = _
          rw [Core.Finite.CertifiedTableAggregation.binaryRateFloor,
            if_neg (Nat.ne_of_gt flatPos)]
        rw [rateDef]
        rcases Nat.eq_zero_or_pos ((safe - 1) / flat) with qZero | qPos
        · rw [qZero]
          simp only [Nat.log2_zero, pow_zero, one_mul]
          omega
        · calc 2 ^ Nat.log2 ((safe - 1) / flat) * flat
              ≤ ((safe - 1) / flat) * flat :=
                Nat.mul_le_mul_right _ (by
                  simpa [Nat.log2_eq_log_two] using
                    Nat.pow_log_le_self 2 (Nat.ne_of_gt qPos))
            _ ≤ safe - 1 := Nat.div_mul_le_self _ _
      have compounded : 2 ^ (data.windowRate * scales) * flat ^ scales ≤
          safe ^ scales - 1 := by
        have step : (2 ^ data.windowRate * flat) ^ scales ≤
            (safe - 1) ^ scales :=
          Nat.pow_le_pow_left rateBound scales
        rw [mul_pow, ← pow_mul] at step
        refine step.trans ?_
        -- `(S − 1)^s ≤ S^s − 1` for `S ≥ 1`, `s ≥ 1`.
        have onePos : 1 ≤ safe := le_trans (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt flatPos)) improves
        have : (safe - 1) ^ scales + 1 ≤ safe ^ scales := by
          have := Nat.pow_le_pow_left (Nat.sub_le safe 1) scales
          have strict : (safe - 1) ^ scales < safe ^ scales :=
            Nat.pow_lt_pow_left (by omega) (Nat.ne_of_gt scalesPos)
          omega
        omega
      have flatPowPos : 0 < flat ^ scales := pow_pos flatPos scales
      have divBound : 2 ^ (data.windowRate * scales) ≤
          (safe ^ scales - 1) / flat ^ scales :=
        (Nat.le_div_iff_mul_le flatPowPos).mpr compounded
      have quotientPos : (safe ^ scales - 1) / flat ^ scales ≠ 0 :=
        Nat.ne_of_gt (lt_of_lt_of_le (Nat.one_le_two_pow) divBound)
      exact (Nat.le_log2 quotientPos).mpr divBound
    · -- `flat = safe`: the registered rate is `0`.
      have rateZero : data.windowRate = 0 := by
        rw [windowRate_eq_barrier]
        show Core.Finite.CertifiedTableAggregation.binaryRateFloor
          barrier.table = 0
        rw [Core.Finite.CertifiedTableAggregation.binaryRateFloor,
          if_neg (Nat.ne_of_gt flatPos)]
        have : (safe - 1) / flat = 0 :=
          Nat.div_eq_of_lt (by omega)
        change Nat.log2 ((safe - 1) / flat) = 0
        rw [this]
        rfl
      simp [rateZero]
  let Coordinate := Graph.DeclaredSignature.Coordinate
    object.Vertex
      (Fin bits × Finset object.Vertex)
  let package : Finset object.Vertex →
      Finset Coordinate := fun window =>
    Finset.univ.image fun bit =>
      Graph.DeclaredSignature.Coordinate.base
        .windowLabel (bit, window) window
  let family := packing.biUnion package
  have packageCard : ∀ window, (package window).card = bits := by
    intro window
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro left _ right _ equality
      cases equality
      rfl
  have packagesDisjoint :
      ∀ left ∈ packing, ∀ right ∈ packing, left ≠ right →
        Disjoint (package left) (package right) := by
    intro left _leftMem right _rightMem different
    rw [Finset.disjoint_left]
    intro coordinate leftMember rightMember
    obtain ⟨leftBit, _, leftEq⟩ := Finset.mem_image.mp leftMember
    obtain ⟨rightBit, _, rightEq⟩ := Finset.mem_image.mp rightMember
    rw [← leftEq] at rightEq
    have supportEq := congrArg
      Graph.DeclaredSignature.Coordinate.support rightEq
    simp only [Graph.DeclaredSignature.Coordinate.support_base]
      at supportEq
    exact different supportEq.symm
  have familyCard : family.card = bits * packing.card := by
    rw [Finset.card_biUnion]
    · simp_rw [packageCard]
      simp [Nat.mul_comm]
    · intro left leftMem right rightMem different
      exact packagesDisjoint left leftMem right rightMem different
  refine ⟨(fun window _member => by
      simpa only [package, bits] using packageCard window),
    (by simpa only [package] using packagesDisjoint),
    (by simpa only [family, bits] using familyCard),
    (by simpa only [bits, scales] using rateLe), ?_, ?_⟩
  · intro declared _functional
    by_contra reducing
    rcases declared.localize reducing with replacement |
      ⟨representative, smaller, baseline, transfer⟩
    · exact noReplacement declared.support replacement
    · exact selected.1 (transfer (selected.2 representative smaller baseline))
  · intro _baselineIndependent
    intro declared _functional
    by_contra reducing
    rcases declared.localize reducing with replacement |
      ⟨representative, smaller, baselineObject, transfer⟩
    · exact noReplacement declared.support replacement
    · exact selected.1
        (transfer (selected.2 representative smaller baselineObject))

/-- **Node `[22]`, `def:cold-window-ledger`.**  The canonical maximal packing
splits into the canonical hot family (a maximal realized subfamily, or empty)
and its cold complement. -/
theorem hotColdPartition_canonical (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    HotColdWindowStatement data object := by
  classical
  let packing := canonicalWindowPacking data object
  have packingFacts :
      object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder :=
    ⟨(canonicalWindowPacking_spec data object).1,
      (canonicalWindowPacking_spec data object).2.1⟩
  let hot := canonicalHotWindows data object
  let cold := canonicalColdWindows data object
  have hotFacts :
      hot ⊆ packing ∧
        (WindowFamilyRealized data object hot ∨
          (hot = ∅ ∧ ¬ WindowFamilyRealized data object ∅)) ∧
        ∀ other : Finset (Finset object.Vertex), other ⊆ packing →
          WindowFamilyRealized data object other →
            other.card ≤ hot.card :=
    Classical.choose_spec (exists_maximal_windowFamilyRealized data object)
  show IsHotColdWindowPartition data object packing hot cold
  refine ⟨packingFacts.1, packingFacts.2, ?_, hotFacts, ?_, ?_, ?_⟩
  · intro support window
    exact object.exists_mem_not_disjoint_of_card_eq
      data.windowOrder_pos packingFacts.1 packingFacts.2 window
  · intro window
    simp [cold, packing, hot, canonicalColdWindows]
  · exact Finset.disjoint_sdiff
  · intro window
    constructor
    · intro member
      by_cases inHot : window ∈ hot
      · exact Or.inl inHot
      · exact Or.inr (by
          simp [cold, packing, hot, canonicalColdWindows, member, inHot])
    · intro member
      rcases member with member | member
      · exact hotFacts.1 member
      · exact (Finset.mem_sdiff.mp member).1

/-- **Node `[23]`, the live-hot entropy comparison.**  The canonical hot family
either has its package realized by labelled skeletons, whose state count the
skeleton budget dominates, or is empty; either way the exact cap
`2^{rate·scales·|𝒫_hot|} ≤ skeletonBudget` holds. -/
theorem barrierCap_of_hotColdPartition (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (hotColdPartition : HotColdWindowStatement data object)
    (skeletonDominates : SkeletonDominatesStatement object)
    (windowPackageSeparated : WindowPackageSeparatedStatement data object) :
    BarrierCapStatement data object := by
  change 2 ^ (data.windowRate *
      data.separatedScaleCount object.vertexCount *
      (canonicalHotWindows data object).card) ≤
    Graph.skeletonBudget object
  have split := hotColdPartition
  have dominates := skeletonDominates
  have package := windowPackageSeparated
  obtain
    ⟨_valid, _attains, _maximal, hotFacts, _coldIff, _disjoint, _cover⟩ :=
      split
  obtain ⟨_hotSubset, retained, _hotMaximal⟩ := hotFacts
  obtain ⟨_packageCard, _packagesDisjoint, _familyCard, rateLe, _⟩ := package
  have exponentLe :
      data.windowRate * data.separatedScaleCount object.vertexCount *
          (canonicalHotWindows data object).card ≤
        windowPackageBits data object *
          (canonicalHotWindows data object).card :=
    Nat.mul_le_mul_right _ rateLe
  rcases retained with
    ⟨State, stateOf, packageStates, _retainedCode⟩ |
      ⟨hotEmpty, _emptyUnrealized⟩
  · have realizedBound := dominates.2 State stateOf
    exact (Nat.pow_le_pow_right (by norm_num) exponentLe).trans
      (packageStates.trans realizedBound)
  · rw [hotEmpty]
    simp only [Finset.card_empty, Nat.mul_zero, pow_zero]
    exact Graph.skeletonBudget_pos object

/-- **The relabelling density cap.**  For relabellings fixing the packed window
support pointwise, the invariant-state image times the remainder factorial is
at most the skeleton count times the stabilizer bound. -/
theorem relabelingDensityCap_of_orbitCount (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    RelabelingDensityCapStatement data object :=
  fun labels => by
    dsimp only
    let packing := canonicalWindowPacking data object
    intro State stateDecidable skeletons state stabilizerBound
      closed invariant bounded
    classical
    letI : DecidableEq State := stateDecidable
    have cap :=
      Core.FiniteRelabelingOrbit.card_image_mul_card_group_le_card_mul_stabilizerBound
        skeletons state stabilizerBound closed invariant bounded
    rw [Graph.LabelledRelabeling.card_fixedSupportPermutations] at cap
    have complementCard :
        object.vertexCount -
            ((object.windowSupport packing).map
              labels.toEmbedding).card =
          (Finset.univ \ ((object.windowSupport packing).map
            labels.toEmbedding)).card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
        Finset.card_map]
      simp only [Fintype.card_fin]
    rw [complementCard] at cap
    exact cap

end Hypostructure.Graph.Contracts.Spine
