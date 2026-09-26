import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## The route-8 rate failure, `rem:route8-carrier-margin` read exactly

When the private-carrier rate `τ < 3/13` of node `[120]` fails on a residual that
already carries the hot/cold ledger of the fixed packing, the manuscript's
delicate density interval (row 2 of `tab:cold-branch-ledger`) is handled by the
hot/cold pass; in exact form its residue is decided by the cold family: if the
cold family is nonempty, the failure is carried by cold windows whose selected
corridors are charged as in `[174]`--`[177]` (absorbed germs or genuine germs);
if it is empty, every packed window is hot at the exact skeleton budget and the
rate still fails — the exact budget-edge corner.  This is that decision on the
literal residual. -/
noncomputable def coldFamilyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .hotColdPartition) known]
    (positiveFresh : K .coldFamilyPositive ∉ known)
    (emptyFresh : K .coldFamilyEmpty ∉ known) :
    Decision (K .coldFamilyPositive) (K .coldFamilyEmpty) previous := by
  classical
  let _split := (previous.get (K .hotColdPartition)).down
  exact Decision.run previous (K .coldFamilyPositive) (K .coldFamilyEmpty)
    `Hypostructure.Graph.Strategy.Spine.coldFamilyDichotomy
    (if positive : 0 < (canonicalColdWindows data current.object).card then
      .inl ⟨positive⟩
    else
      .inr ⟨Nat.eq_zero_of_not_pos positive⟩)
    positiveFresh emptyFresh

/-! ## `thm:cold-branch-quantitative-closure`: no terminal cold residual

With the germs routed and the table closed, no local terminal cold pattern
remains on this residual: the branch is closed by routing, exactly as the
manuscript's Part XI leaves are drawn. -/
@[reducible] noncomputable def coldBranchClosedRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldBranchClosed
    { Requires := [K .coldGermExtraction, K .coldGermRouted,
        K .coldSameInterfaceTable]
      Produces := [K .coldBranchClosed]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let extraction := (inputs.get (K .coldGermExtraction)).down
      let routed := (inputs.get (K .coldGermRouted)).down
      let table := (inputs.get (K .coldSameInterfaceTable)).down
      .cons (key := K .coldBranchClosed)
        ⟨Graph.ColdCorridor.noTerminalColdResidual_of_routing extraction.2
          (fun germ shorter =>
            let routedGerm := routed.2 germ shorter
            ⟨routedGerm.1, routedGerm.2.1⟩)
          table.2.1 table.2.2.1⟩
        .nil)

/-! ## Node `[24]`: `prop:p13-density`, after the cold branch

The manuscript's `[24]` reads "bounded cold-mass return from [153]:
`θ ≤ θ_win + o(1)`; high entropy: `θ ≤ 0.01198542083…`".  On the `[153]` bounded arm the cold mass is
`C ≤ (1 + (threshold+1)·B_cold)·σ(G)`; with
`lem:hot-failure-cold-mass` (`K .coldMass`,
`bitRate·|𝒫| ≤ bitRate·C + allowance`) and the near-cubic surplus bound
`σ(G) ≤ T(n)` (`K .coldAmbientCubic`) this is the manuscript's window-only
density cap with its exact `o(1)`. -/
@[reducible] noncomputable def densityBudgetRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.finiteDensityBudget
    { Requires := [K .coldMass, K .coldMassBounded, K .coldAmbientCubic,
        K .hotColdPartition]
      Produces := [K .densityCap]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let mass := (inputs.get (K .coldMass)).down
      let bounded := (inputs.get (K .coldMassBounded)).down
      let cubic := (inputs.get (K .coldAmbientCubic)).down
      let split := (inputs.get (K .hotColdPartition)).down
      .cons (key := K .densityCap)
        ⟨by
          classical
          let object := inputs.current.object
          let packing := canonicalWindowPacking data object
          let cold := canonicalColdWindows data object
          let perWindow := coldInteriorBranchExcess data
          have perWindowPos : 0 < perWindow := by
            have order := data.five_le_windowOrder
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
                  simp only [Data.densitySlack, highLoss, overlap]; ring
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
                  data.surplusThreshold object.vertexCount := by ring⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
