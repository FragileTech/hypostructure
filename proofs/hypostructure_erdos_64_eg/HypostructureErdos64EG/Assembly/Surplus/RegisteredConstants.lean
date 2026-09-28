import HypostructureErdos64EG.Assembly.Basic

/-!
# Assembly: the registered numbers behind the `[20a]` budget

Identities of the registered presentation `spineData` (not facts about any
graph, so not ledger keys): the routing-label count, `M₀`, `S = M₀ + 1`,
`C_sp = 4 + 22·M₀`, the value of `C_sp`, and the pair-deficit coefficient
`C² − 3C − 2M₀C − 2S − 16M₀` of `CappedPairDeficitStatement` with its lower
bound `440·M₀²`.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph.SameTokenBlockerRoles

universe u

theorem registered_routingLabelBound_value :
    (spineData.{u}).toParameters.routingLabelBound = 20639121408 := by decide

theorem registered_homogeneousCap_value :
    homogeneousTokenCap (spineData.{u}).toParameters.routingLabelBound =
      30670079938836792606720 := by decide

/-- `M₀ = Q_st·Q_geom·(2Q_geom − 1)` with `Q_st = 36`. -/
theorem registered_homogeneousCap_eq :
    homogeneousTokenCap (spineData.{u}).toParameters.routingLabelBound =
      36 * (spineData.{u}).toParameters.routingLabelBound *
        (2 * (spineData.{u}).toParameters.routingLabelBound - 1) := by
  rw [registered_homogeneousCap_value, registered_routingLabelBound_value]

theorem registered_surplusScale_eq :
    (spineData.{u}).toParameters.surplusScale =
      homogeneousTokenCap (spineData.{u}).toParameters.routingLabelBound + 1 := rfl

theorem registered_spineScale_eq :
    (spineData.{u}).toParameters.spineScale =
      4 + 22 * homogeneousTokenCap (spineData.{u}).toParameters.routingLabelBound := by
  simp only [Parameters.spineScale, registeredSpineScale, registeredHomogeneousCap]
  have h3 : (spineData.{u}).toParameters.threshold = 3 := rfl
  rw [h3, registered_surplusScale_eq]; ring

/-- The deficit coefficient `K = C² − 3C − 2M₀C − 2S − 16M₀` (≥ 440·M₀²) is
positive. -/
theorem registered_pairDeficitCoefficient_value :
    ((spineData.{u}).toParameters.spineScale : ℤ) ^ 2
        - 3 * (spineData.{u}).toParameters.spineScale
        - 2 * (homogeneousTokenCap (spineData.{u}).toParameters.routingLabelBound : ℤ) *
            (spineData.{u}).toParameters.spineScale
        - 2 * (spineData.{u}).toParameters.surplusScale
        - 16 * (homogeneousTokenCap (spineData.{u}).toParameters.routingLabelBound : ℤ) =
      413887673520041193494544894373402613429808660482 ∧
    440 * (30670079938836792606720 : ℤ) ^ 2 ≤
      413887673520041193494544894373402613429808660482 := by
  rw [registered_spineScale_eq, registered_surplusScale_eq, registered_homogeneousCap_value]
  norm_num

theorem registered_spineScale_value :
    (spineData.{u}).toParameters.spineScale = 674741758654409437347844 := by
  rw [registered_spineScale_eq, registered_homogeneousCap_value]

end HypostructureErdos64EG
