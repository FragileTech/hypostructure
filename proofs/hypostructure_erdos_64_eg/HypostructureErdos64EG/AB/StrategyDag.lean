import HypostructureErdos64EG.AB.Definition
import HypostructureErdos64EG.StrategyDag

/-!
# Shared official EG topology for the A/B target

This module elaborates the one authored official blueprint against the A/B
problem registry.  The shared blueprint includes the registered
`finiteStateNetChargeContinuation` on the node-[56] capacity residual.  The
density-overflow side remains a literal residual until the paper's Type-B and
route-8 support ledgers have been produced upstream.  There is no standalone
comparison DAG.
-/

namespace HypostructureErdos64EG.AB

open Hypostructure
open Hypostructure.Core.Strategy.Dag

noncomputable def strategyDag : Program definition.data :=
  Program.ofBlueprint (erdosOfficialBlueprint%
    ⟨0, by simp [definition]⟩     -- fanSafeScan       scans 0
    ⟨1, by simp [definition]⟩     -- certSplit         dichotomies 1
    ⟨2, by simp [definition]⟩     -- b2Split           dichotomies 2
    ⟨1, by simp [definition]⟩     -- fanMass           baselineDemand 1
    ⟨1, by simp [definition]⟩     -- degreeFour        scans 1
    ⟨2, by simp [definition]⟩     -- hybridEntry       scans 2
    ⟨3, by simp [definition]⟩     -- bridgeDeficit     scans 3
    ⟨3, by simp [definition]⟩     -- directCycleSplit  dichotomies 3
    ⟨4, by simp [definition]⟩     -- typeASaturated    dichotomies 4   [89]
    ⟨5, by simp [definition]⟩     -- typeAVisible      dichotomies 5   [93]
    ⟨6, by simp [definition]⟩     -- typeAExitOne      dichotomies 6   [95]
    ⟨7, by simp [definition]⟩     -- typeAExitTwo      dichotomies 7   [97]
    ⟨8, by simp [definition]⟩     -- typeAExitThree    dichotomies 8   [99]
    ⟨9, by simp [definition]⟩     -- typeAExitFour     dichotomies 9   [101]
    ⟨10, by simp [definition]⟩    -- typeAExitFive     dichotomies 10   [103]
    ⟨11, by simp [definition]⟩    -- typeAExitSix      dichotomies 11   [105]
    ⟨12, by simp [definition]⟩    -- typeAExitSeven    dichotomies 12   [107]
    ⟨0, by simp [definition]⟩)    -- typeARoute8      route8Closures 0 [111]-[124]

end HypostructureErdos64EG.AB
