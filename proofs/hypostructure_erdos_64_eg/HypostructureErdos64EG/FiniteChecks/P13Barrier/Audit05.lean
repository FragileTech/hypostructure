import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit04

namespace HypostructureErdos64EG.FiniteChecks.P13Barrier

open Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! Independent audit shard for connector length `5`. -/

theorem p13MultiScaleRows_codeAudit_05 : ∀ source target : Fin 399,
    (row 5 source).getLsb target =
      semanticRelation 5 source target := by
  native_decide

theorem p13MultiScaleSafeCounts_audit_05 : ∀ right : Fin 15,
    if 0 < 5 ∧ 0 < right.1 ∧ 5 + right.1 ≤ 14 then
      safeCount 5 right.1 = profile.safeCount 5 right.1
    else safeCount 5 right.1 = 0 := by
  intro right
  fin_cases right <;> native_decide

theorem p13MultiScaleFlatCounts_audit_05 : ∀ right : Fin 15,
    if 0 < 5 ∧ 0 < right.1 ∧ 5 + right.1 ≤ 14 then
      flatCount 5 right.1 = profile.flatCount 5 right.1
    else flatCount 5 right.1 = 0 := by
  intro right
  fin_cases right <;> native_decide

end HypostructureErdos64EG.FiniteChecks.P13Barrier
