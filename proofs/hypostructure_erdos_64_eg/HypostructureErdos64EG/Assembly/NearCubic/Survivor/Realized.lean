import Hypostructure.Graph.Strategy.ColdCorridorRows.ColdFamilyClosure
import Hypostructure.Graph.Strategy.SpineRows.Bridgeless
import Hypostructure.Graph.Strategy.SpineRows.Route8RateFromColdBelow
import HypostructureErdos64EG.Assembly.NearCubic.ColdPass
import HypostructureErdos64EG.Assembly.NearCubic.Spine

/-!
# Assembly: NearCubic / Survivor / Realized

The yes-arm of `[158]`: the hot/cold split `[22]` and the cold branch
`[145]`--`[157]` of Part XI on the realized-package residual.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
/-- **The realized-package arm of `[158]`.**  `[22]`--`[23]`, then `[146]`
(`θ < 1/78`).  Its yes arm `[147]`: the route-8 private-carrier inequality
`τ(θ) < 3/13` is `K .coldRoute8Below` read through `|∂R| ≤ 15p + σ_W`
(`route8RateFromColdBelowRow`); the arm runs the spine's route-8 closure
`[25]`--`[124]` with that inequality in place of `[24]`.  Its no arm runs
`[148]`--`[152]` and decides `[153]`: the bounded arm returns through `[24]`
(`densityBudgetRow`, `prop:p13-density` after closure) to `[25]`; the linear arm
extracts the configuration family and decides `[154]`.  G1 closes at `[155]`;
G2 `[156]` and the silent arm `[157]` publish the local cold-terminal exclusion
of `thm:cold-branch-quantitative-closure`, retained at `[187]`. -/
-- EG-NODE [146] \(\theta<1/78\)?
-- EG-NODE [147] route-8 private-incidence collision closes
-- EG-NODE [24] bounded cold-mass return from [153]: $\theta\le\theta_{\rm win}+o(1)$; high entropy: $\theta\le0.01198542083\ldots$
noncomputable def Assembly.Internal.nearCubicRealized
    {selected : EGInput.{u}}
    (enumerated : ExactLedger EGInput.{u} selected
      [K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated,
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra,
       K .maximalPacking, K .windowPresent, K .uncompressible, K .replacementExclusion,
       K .targetCompleteContextUniversality, K .degreeProfileFibres,
       K .cycleRankConstraint,
       K .tightEndpoint, K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
       K .cubicBaseline,
       K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  let cap := nearCubicHotColdCap enumerated
  match coldRoute8Dichotomy (data := spineData) cap
      (by key_fresh) (by key_fresh) with
  | .left belowHistory =>
      let rated :=
        (route8RateFromColdBelowRow (BranchState := BranchState)
            (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
            (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          belowHistory (by key_fresh)
      -- `[149]`--`[152]` are facts of G on this arm too: the cold facts are
      -- published from `[22]`'s cap before the spine, so every arm of `[146]`
      -- carries them.
      let stubbed := nearCubicColdStubFacts rated
      exact nearCubicLargeBudgetColdRate (nearCubicFullRank stubbed)
  | .right atOrAboveHistory =>
      let stubs := nearCubicColdStubs atOrAboveHistory
      match coldMassDichotomy (data := spineData) stubs
          (by key_fresh) (by key_fresh) with
      | .right boundedHistory =>
          let density :=
            (densityBudgetRow (data := spineData)).run boundedHistory
              (by key_fresh)
          exact nearCubicLargeBudgetDensityCap (nearCubicFullRank density)
      | .left linearHistory =>
          -- `[25]`--`[34]` and `[48]` are facts of G on the linear arm too:
          -- the remainder normalization, the external-incidence and wedge
          -- supply, the obstruction rank (its rank-drop arm is Branch D, closed)
          -- and the forced curvature cost.
          let spine := nearCubicFullRank linearHistory
          let cost :=
            (forcedCurvatureCostRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              spine (by key_fresh)
          -- `[58]`'s net-charge localization is a fact of G here too.
          let localized :=
            (netChargeLocalizationRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) spineData).run
              cost (by key_fresh)
          let bridgeless :=
            (bridgelessRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              localized (by key_fresh)
          match nearCubicColdOccurrence (nearCubicColdCorridorState bridgeless) with
          | .inr repeated =>
              -- `[153]`, ¬(★): G's first equal-state pair, returned.
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl repeated))))
          | .inl distinct =>
              let familyOnly := nearCubicColdGermFamily distinct
              -- `[175]`'s per-half-edge split and `[177]`'s fan data are facts
              -- of G on the extracted family here too.
              let split :=
                (absorbedGermSplitRow (data := spineData)).run familyOnly
                  (by key_fresh)
              let family :=
                (absorbedGermFanDataRow (data := spineData)).run split
                  (by key_fresh)
              let unhit := nearCubicColdNoHit family
              match coldGermDistinctionDichotomy (data := spineData) unhit
                  (by key_fresh) (by key_fresh) with
              | .left distinguishedHistory =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl
                    (coldBranchClosedReturn
                      (nearCubicColdTable distinguishedHistory)))))
              | .right silentHistory =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl
                    (coldBranchClosedReturn (nearCubicColdTable silentHistory)))))

end HypostructureErdos64EG
