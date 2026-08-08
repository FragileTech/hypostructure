import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit07

namespace HypostructureErdos64EG.FiniteChecks.P13Barrier

open Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! Independent audit shard for connector length `8`. -/

theorem p13MultiScaleRows_codeAudit_08 : ∀ source target : Fin 399,
    (row 8 source).getLsb target =
      semanticRelation 8 source target := by
  native_decide

theorem p13MultiScaleSafeCounts_audit_08 : ∀ right : Fin 15,
    if 0 < 8 ∧ 0 < right.1 ∧ 8 + right.1 ≤ 14 then
      safeCount 8 right.1 = profile.safeCount 8 right.1
    else safeCount 8 right.1 = 0 := by
  intro right
  fin_cases right <;> native_decide

theorem p13MultiScaleFlatCounts_audit_08 : ∀ right : Fin 15,
    if 0 < 8 ∧ 0 < right.1 ∧ 8 + right.1 ≤ 14 then
      flatCount 8 right.1 = profile.flatCount 8 right.1
    else flatCount 8 right.1 = 0 := by
  intro right
  fin_cases right <;> native_decide

end HypostructureErdos64EG.FiniteChecks.P13Barrier
