import Hypostructure.Graph.Statements.SparseExitReadings
import Hypostructure.Graph.Contracts.Spine.SparseExitResidual

/-!
# Contracts: the edge switches of G

Proof-agnostic contract lemmas for `Statements/SparseExitReadings.lean`, one
`<statement>_holds` per statement.  Each is stated over a `Graph.FiniteObject`
with the registered `Parameters` as a parameter; its hypotheses are exactly
ledger facts: the selection (target avoidance), the presentation laws
(`δ = 3`), the baseline, the tight endpoint and slack independence,
`surplusAbove` and `C + 1 ≤ ⌈√n⌉`.  The mathematics is in the vocabulary-free
module `Graph/EdgeSwitchPaths`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine.SparseExitReadings

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u v

set_option linter.unusedVariables false

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-! ## Edge switches of G -/

theorem highSurplusConfiguration_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (scale : Graph.TokenLoad.quadraticSafetyScale ≤ data.spineScale)
    (above : SurplusAboveStatement data object)
    (ceil : CeilSqrtAboveScaleStatement data object) :
    HighSurplusConfigurationStatement data object := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  have base : ∀ v, 3 ≤ object.degree v := fun v => by
    have := le_trans baseline (object.minDegree_le_degree v)
    omega
  have σeq := SparseOrderArithmetic.sigma_eq_sum object base
  have above' : data.spineScale * Core.ceilSqrt object.vertexCount <
      object.degreeSurplus data.threshold := above
  have ceil' : data.spineScale + 1 ≤ Core.ceilSqrt object.vertexCount := ceil
  have q : Graph.TokenLoad.quadraticSafetyScale = 20 := rfl
  have two : 2 ≤ object.degreeSurplus 3 := by
    rw [three] at above'
    have s20 : 20 ≤ data.spineScale := q ▸ scale
    have one : 1 ≤ Core.ceilSqrt object.vertexCount := by omega
    have prod : 20 * 1 ≤ data.spineScale * Core.ceilSqrt object.vertexCount :=
      Nat.mul_le_mul s20 one
    omega
  unfold HighSurplusConfigurationStatement
  rw [three]
  by_contra hn
  push Not at hn
  obtain ⟨lt5, uniq⟩ := hn
  have le1 : Finset.univ.sum (fun v => object.degree v - 3) ≤ 1 := by
    by_cases ex : ∃ h, object.degree h = 3 + 1
    · obtain ⟨h, hh⟩ := ex
      rw [Finset.sum_eq_single h]
      · omega
      · intro v _ vh
        have := uniq h v (Ne.symm vh) hh
        have := lt5 v
        have := base v
        omega
      · simp
    · push Not at ex
      have : Finset.univ.sum (fun v => object.degree v - 3) = 0 :=
        Finset.sum_eq_zero fun v _ => by
          have := lt5 v; have := base v; have := ex v; omega
      omega
  omega

theorem highEndpointSwitch_holds (slack : SlackIndependentStatement data object)
    (twoSwitch : TwoSwitchForcedPathStatement data object)
    (sameVertex : SameVertexSwitchForcedPathStatement data object)
    (config : HighSurplusConfigurationStatement data object) :
    HighEndpointSwitchStatement data object := by
  intro h c dh dc a
  by_cases d5 : data.threshold + 2 ≤ object.degree h
  · left
    obtain ⟨u, hu, uc, cu⟩ := EdgeSwitchPaths.exists_nonadj_nbr dc dh
    obtain ⟨p, pp, ok, -⟩ := sameVertex a hu uc.symm cu d5
    exact ⟨d5, u, hu, uc, cu, p, pp, ok⟩
  · right
    have second : ∃ h₂, h₂ ≠ h ∧ data.threshold + 1 ≤ object.degree h₂ := by
      rcases config with ⟨h', h5⟩ | ⟨h₁, h₂, ne, e1, e2⟩
      · exact ⟨h', fun e => by subst e; omega, by omega⟩
      · by_cases e : h₁ = h
        · exact ⟨h₂, fun e' => ne (e.trans e'.symm), by omega⟩
        · exact ⟨h₁, e, by omega⟩
    obtain ⟨h₂, h2ne, d2⟩ := second
    obtain ⟨u₂, hu₂, u2c, cu₂⟩ := EdgeSwitchPaths.exists_nonadj_nbr dc d2
    have ch₂ : c ≠ h₂ := fun e => by subst e; omega
    have hu : h ≠ u₂ := fun e => slack h h₂ (by omega) (by omega) (by rw [e]; exact hu₂.symm)
    obtain ⟨p, pp, ok⟩ := twoSwitch a.symm hu₂.symm u2c.symm ch₂ hu (Ne.symm h2ne) cu₂
      dh d2
    exact ⟨h₂, u₂, h2ne, d2, hu₂.symm, u2c, cu₂, p, pp, ok⟩

end Hypostructure.Graph.Contracts.Spine.SparseExitReadings
