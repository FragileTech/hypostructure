import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Node `[21]`: the separated window package

`lem:p13-window-package`.  For every selected dyadic scale, the complete
certified table contributes the ratio between the products of its safe and
flat columns.  The package compounds that exact ratio across all scales and
only then takes the integer logarithm.  This is the manuscript's
`(c₁₃ - o(1)) p₁₃ log₂ n` exponent; taking the integer floor before
scale aggregation would incorrectly replace `c₁₃` by `118`.

The scale factor is not decorative: without it the demand grows a whole
`log₂ n` slower than the manuscript's, and the cap node `[22]`--`[24]` derives
from it degrades to `θ ≲ 1.5·log₂ n / rate`, which bounds nothing as `n` grows.

The cap arm carries `lem:variable-edge-budget` with it: the budget the arm
retained is stable when the edge count is only known to lie in an admissible
family, because the exact stratum is one of the family's and the family's own
union bound dominates it (`sum_edgeStratumCount_le_variableEdgeBudget` is the
summed form of the same count).  That is what makes the retained cap survive
`rem:budget-robustness` rather than depending on the exact `m`.

`lem:p13-window-package` is proved on the literal near-cubic residual.  The
label-injectivity clauses are refuted through the ledger's `lem:replacement`
fact (`K .replacementExclusion`) and the selection's minimality, exactly as
`DeclaredQuotient.localize` splits them. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def windowPackageRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.windowPackage
    { Requires := [K .maximalPacking, K .replacementExclusion, K .selection]
      Produces := [K .windowPackageSeparated]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .windowPackageSeparated)
        (show Value BranchState Presentation presentation data
            .windowPackageSeparated inputs.current from
          ⟨by
            classical
            simp only [Holds]
            let noReplacement := (inputs.get (K .replacementExclusion)).down
            let selected := (inputs.get (K .selection)).down
            obtain ⟨_positive, packing, valid, maximum, maximal⟩ :=
              (inputs.get (K .maximalPacking)).down
            refine ⟨packing, valid, maximum, maximal, ?_⟩
            let barrier := data.windowBarrier
            letI := barrier.indexFintype
            let scales := data.separatedScaleCount
              inputs.current.object.vertexCount
            let safe := Core.Finite.CertifiedTableAggregation.safeProduct
              barrier.table
            let flat := Core.Finite.CertifiedTableAggregation.flatProduct
              barrier.table
            let bits := windowPackageBits data inputs.current.object
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
                    rw [data.windowRate_eq_barrier]
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
                  rw [data.windowRate_eq_barrier]
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
              inputs.current.object.Vertex
                (Fin bits × Finset inputs.current.object.Vertex)
            let package : Finset inputs.current.object.Vertex →
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
            · intro BaselineCoordinate baseline baselineSupport
                _baselineIndependent
              intro declared _functional
              by_contra reducing
              rcases declared.localize reducing with replacement |
                ⟨representative, smaller, baselineObject, transfer⟩
              · exact noReplacement declared.support replacement
              · exact selected.1
                  (transfer (selected.2 representative smaller baselineObject))⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
