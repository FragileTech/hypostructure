import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit01

namespace HypostructureErdos64EG.FiniteChecks.P13Barrier

open Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! Independent audit shard for connector length `2`. -/

theorem p13MultiScaleRows_codeAudit_02 : ∀ source target : Fin 399,
    (row 2 source).getLsb target =
      semanticRelation 2 source target := by
  native_decide

theorem p13MultiScaleSafeCounts_audit_02 : ∀ right : Fin 15,
    if 0 < 2 ∧ 0 < right.1 ∧ 2 + right.1 ≤ 14 then
      safeCount 2 right.1 = profile.safeCount 2 right.1
    else safeCount 2 right.1 = 0 := by
  intro right
  fin_cases right <;> native_decide

theorem p13MultiScaleFlatCounts_audit_02 : ∀ right : Fin 15,
    if 0 < 2 ∧ 0 < right.1 ∧ 2 + right.1 ≤ 14 then
      flatCount 2 right.1 = profile.flatCount 2 right.1
    else flatCount 2 right.1 = 0 := by
  intro right
  fin_cases right <;> native_decide

end HypostructureErdos64EG.FiniteChecks.P13Barrier
