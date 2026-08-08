import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit06

namespace HypostructureErdos64EG.FiniteChecks.P13Barrier

open Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! Independent audit shard for connector length `7`. -/

theorem p13MultiScaleRows_codeAudit_07 : ∀ source target : Fin 399,
    (row 7 source).getLsb target =
      semanticRelation 7 source target := by
  native_decide

theorem p13MultiScaleSafeCounts_audit_07 : ∀ right : Fin 15,
    if 0 < 7 ∧ 0 < right.1 ∧ 7 + right.1 ≤ 14 then
      safeCount 7 right.1 = profile.safeCount 7 right.1
    else safeCount 7 right.1 = 0 := by
  intro right
  fin_cases right <;> native_decide

theorem p13MultiScaleFlatCounts_audit_07 : ∀ right : Fin 15,
    if 0 < 7 ∧ 0 < right.1 ∧ 7 + right.1 ≤ 14 then
      flatCount 7 right.1 = profile.flatCount 7 right.1
    else flatCount 7 right.1 = 0 := by
  intro right
  fin_cases right <;> native_decide

end HypostructureErdos64EG.FiniteChecks.P13Barrier
