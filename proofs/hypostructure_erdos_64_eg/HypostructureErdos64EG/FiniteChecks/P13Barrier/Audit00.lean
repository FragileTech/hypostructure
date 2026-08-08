import HypostructureErdos64EG.FiniteChecks.P13Barrier.Certificate

namespace HypostructureErdos64EG.FiniteChecks.P13Barrier

open Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! Independent audit shard for connector length `0`. -/

theorem p13MultiScaleRows_codeAudit_00 : ∀ source target : Fin 399,
    (row 0 source).getLsb target =
      semanticRelation 0 source target := by
  native_decide

theorem p13MultiScaleSafeCounts_audit_00 : ∀ right : Fin 15,
    if 0 < 0 ∧ 0 < right.1 ∧ 0 + right.1 ≤ 14 then
      safeCount 0 right.1 = profile.safeCount 0 right.1
    else safeCount 0 right.1 = 0 := by
  intro right
  fin_cases right <;> native_decide

theorem p13MultiScaleFlatCounts_audit_00 : ∀ right : Fin 15,
    if 0 < 0 ∧ 0 < right.1 ∧ 0 + right.1 ≤ 14 then
      flatCount 0 right.1 = profile.flatCount 0 right.1
    else flatCount 0 right.1 = 0 := by
  intro right
  fin_cases right <;> native_decide

end HypostructureErdos64EG.FiniteChecks.P13Barrier
