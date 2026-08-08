import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit10

namespace HypostructureErdos64EG.FiniteChecks.P13Barrier

open Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! Independent audit shard for connector length `11`. -/

theorem p13MultiScaleRows_codeAudit_11 : ∀ source target : Fin 399,
    (row 11 source).getLsb target =
      semanticRelation 11 source target := by
  native_decide

theorem p13MultiScaleSafeCounts_audit_11 : ∀ right : Fin 15,
    if 0 < 11 ∧ 0 < right.1 ∧ 11 + right.1 ≤ 14 then
      safeCount 11 right.1 = profile.safeCount 11 right.1
    else safeCount 11 right.1 = 0 := by
  intro right
  fin_cases right <;> native_decide

theorem p13MultiScaleFlatCounts_audit_11 : ∀ right : Fin 15,
    if 0 < 11 ∧ 0 < right.1 ∧ 11 + right.1 ≤ 14 then
      flatCount 11 right.1 = profile.flatCount 11 right.1
    else flatCount 11 right.1 = 0 := by
  intro right
  fin_cases right <;> native_decide

end HypostructureErdos64EG.FiniteChecks.P13Barrier
