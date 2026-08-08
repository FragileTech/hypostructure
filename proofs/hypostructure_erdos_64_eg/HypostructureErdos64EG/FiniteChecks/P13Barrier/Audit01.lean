import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit00

namespace HypostructureErdos64EG.FiniteChecks.P13Barrier

open Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! Independent audit shard for connector length `1`. -/

theorem p13MultiScaleRows_codeAudit_01 : ∀ source target : Fin 399,
    (row 1 source).getLsb target =
      semanticRelation 1 source target := by
  native_decide

theorem p13MultiScaleSafeCounts_audit_01 : ∀ right : Fin 15,
    if 0 < 1 ∧ 0 < right.1 ∧ 1 + right.1 ≤ 14 then
      safeCount 1 right.1 = profile.safeCount 1 right.1
    else safeCount 1 right.1 = 0 := by
  intro right
  fin_cases right <;> native_decide

theorem p13MultiScaleFlatCounts_audit_01 : ∀ right : Fin 15,
    if 0 < 1 ∧ 0 < right.1 ∧ 1 + right.1 ≤ 14 then
      flatCount 1 right.1 = profile.flatCount 1 right.1
    else flatCount 1 right.1 = 0 := by
  intro right
  fin_cases right <;> native_decide

end HypostructureErdos64EG.FiniteChecks.P13Barrier
