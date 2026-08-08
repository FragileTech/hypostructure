import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit02

namespace HypostructureErdos64EG.FiniteChecks.P13Barrier

open Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! Independent audit shard for connector length `3`. -/

theorem p13MultiScaleRows_codeAudit_03 : ∀ source target : Fin 399,
    (row 3 source).getLsb target =
      semanticRelation 3 source target := by
  native_decide

theorem p13MultiScaleSafeCounts_audit_03 : ∀ right : Fin 15,
    if 0 < 3 ∧ 0 < right.1 ∧ 3 + right.1 ≤ 14 then
      safeCount 3 right.1 = profile.safeCount 3 right.1
    else safeCount 3 right.1 = 0 := by
  intro right
  fin_cases right <;> native_decide

theorem p13MultiScaleFlatCounts_audit_03 : ∀ right : Fin 15,
    if 0 < 3 ∧ 0 < right.1 ∧ 3 + right.1 ≤ 14 then
      flatCount 3 right.1 = profile.flatCount 3 right.1
    else flatCount 3 right.1 = 0 := by
  intro right
  fin_cases right <;> native_decide

end HypostructureErdos64EG.FiniteChecks.P13Barrier
