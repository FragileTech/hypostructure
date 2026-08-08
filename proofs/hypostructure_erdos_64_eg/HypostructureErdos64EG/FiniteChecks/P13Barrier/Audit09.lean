import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit08

namespace HypostructureErdos64EG.FiniteChecks.P13Barrier

open Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! Independent audit shard for connector length `9`. -/

theorem p13MultiScaleRows_codeAudit_09 : ∀ source target : Fin 399,
    (row 9 source).getLsb target =
      semanticRelation 9 source target := by
  native_decide

theorem p13MultiScaleSafeCounts_audit_09 : ∀ right : Fin 15,
    if 0 < 9 ∧ 0 < right.1 ∧ 9 + right.1 ≤ 14 then
      safeCount 9 right.1 = profile.safeCount 9 right.1
    else safeCount 9 right.1 = 0 := by
  intro right
  fin_cases right <;> native_decide

theorem p13MultiScaleFlatCounts_audit_09 : ∀ right : Fin 15,
    if 0 < 9 ∧ 0 < right.1 ∧ 9 + right.1 ≤ 14 then
      flatCount 9 right.1 = profile.flatCount 9 right.1
    else flatCount 9 right.1 = 0 := by
  intro right
  fin_cases right <;> native_decide

end HypostructureErdos64EG.FiniteChecks.P13Barrier
