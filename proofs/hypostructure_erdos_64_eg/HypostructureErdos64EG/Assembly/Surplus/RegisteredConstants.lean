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

/-- **The first band at the registered `C_sp`** (Lean improvement, not routed by the
paper): on the strict arm of `[19]`, `K .highSurplusOrder` at the registered presentation
excludes every order `n ≤ C² + C + 1 + t* = 455276440872045312844002793268847597983144061160`
(`t* = 170697663182045055264979`, the largest `t` with `125t² + 24t < 8(C² + C + 1)`); in
particular the least admissible order `C(C + 1) + 9` and the whole band `⌈√n⌉ = C + 1` up to
it. -/
theorem registered_firstBand_excluded {object : Graph.FiniteObject.{u}}
    (order : HighSurplusOrderStatement (spineData.{u}).toParameters object) :
    455276440872045312844002793268847597983144061160 < object.vertexCount := by
  have h := order.2 170697663182045055264979 (by rw [registered_spineScale_value]; norm_num)
  rw [registered_spineScale_value] at h
  norm_num at h
  exact h


/-- **The capped arm at the registered presentation** (Lean improvement, not routed by the
paper): with `K = 413887673520041193494544894373402613429808660482 > 0`, `K .freeSideCount`
gives, in the capped arm and for every `Δ ≥ max d`, `n·K ≤ 2σ(τ + 3(Δ − 3))`. -/
theorem registered_cappedForces {object : Graph.FiniteObject.{u}}
    (count : FreeSideCountStatement (spineData.{u}).toParameters object) :
    ∃ (active : Graph.ActiveSurplusDemands
        (Graph.MinimumDegreeAtLeast (spineData.{u}).toParameters.threshold)
        (Graph.HasCycleWithLength (spineData.{u}).toParameters.LengthOK)
        (spineData.{u}).toParameters.LengthOK object (spineData.{u}).toParameters.threshold)
      (c : SurplusCapacity (spineData.{u}).toParameters object)
      (L : Graph.ObjectCapacityLedger object (spineData.{u}).toParameters.threshold
        (spineData.{u}).toParameters.windowOrder c),
      canonicalCapacity (spineData.{u}).toParameters object = some c ∧
      canonicalObjectLedgerAt (spineData.{u}).toParameters object c = some L ∧
      ∀ Δ : ℕ, (∀ v : object.Vertex, object.degree v ≤ Δ) →
        (∀ t ∈ L.presented.tokens, L.presented.load t ≤
            homogeneousTokenCap (spineData.{u}).toParameters.routingLabelBound) →
        (object.vertexCount : ℤ) * 413887673520041193494544894373402613429808660482 ≤
          2 * ((object.degreeSurplus (spineData.{u}).toParameters.threshold *
            (Graph.CapacityFreeSide.tauAt (threshold := (spineData.{u}).toParameters.threshold)
              (Graph.pairResponseChordEnds active) + 3 * (Δ - 3)) : ℕ) : ℤ) := by
  obtain ⟨active, c, L, hc, hL, -, -, -, -, -, -, hΔ⟩ := count
  have hK : pairDeficitCoefficient (spineData.{u}).toParameters =
      413887673520041193494544894373402613429808660482 := by
    unfold pairDeficitCoefficient
    exact registered_pairDeficitCoefficient_value.1
  refine ⟨active, c, L, hc, hL, fun Δ hdeg cap => ?_⟩
  have h := (hΔ Δ hdeg).2 cap (by rw [hK]; norm_num)
  rw [hK] at h
  exact h


/-- **An overloaded extended token, unconditionally** at the registered presentation
(`K > 0`): `K .extOverloadedToken` gives a token of G's canonical capacity presentation with
`load_ext > M₀`. -/
theorem registered_extOverloadedToken {object : Graph.FiniteObject.{u}}
    (token : ExtOverloadedTokenStatement (spineData.{u}).toParameters object) :
    ∃ c : SurplusCapacity (spineData.{u}).toParameters object,
      canonicalCapacity (spineData.{u}).toParameters object = some c ∧
      ∃ t ∈ c.tokens, homogeneousTokenCap (spineData.{u}).toParameters.routingLabelBound <
        Graph.CapacityFreeSide.extLoad (spineData.{u}).toParameters.LengthOK c t := by
  obtain ⟨c, hc, h⟩ := token
  have hK : pairDeficitCoefficient (spineData.{u}).toParameters =
      413887673520041193494544894373402613429808660482 := by
    unfold pairDeficitCoefficient
    exact registered_pairDeficitCoefficient_value.1
  exact ⟨c, hc, h (by rw [hK]; norm_num)⟩

end HypostructureErdos64EG
