import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit00
import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit01
import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit02
import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit03
import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit04
import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit05
import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit06
import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit07
import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit08
import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit09
import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit10
import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit11
import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit12
import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit13
import HypostructureErdos64EG.FiniteChecks.P13Barrier.Audit14

namespace HypostructureErdos64EG.FiniteChecks.P13Barrier

open Certificate

theorem p13MultiScaleRows_codeAudit (length : Fin 15)
    (source target : Fin 399) :
    (row length.1 source).getLsb target =
      semanticRelation length.1 source target := by
  fin_cases length
  · exact p13MultiScaleRows_codeAudit_00 source target
  · exact p13MultiScaleRows_codeAudit_01 source target
  · exact p13MultiScaleRows_codeAudit_02 source target
  · exact p13MultiScaleRows_codeAudit_03 source target
  · exact p13MultiScaleRows_codeAudit_04 source target
  · exact p13MultiScaleRows_codeAudit_05 source target
  · exact p13MultiScaleRows_codeAudit_06 source target
  · exact p13MultiScaleRows_codeAudit_07 source target
  · exact p13MultiScaleRows_codeAudit_08 source target
  · exact p13MultiScaleRows_codeAudit_09 source target
  · exact p13MultiScaleRows_codeAudit_10 source target
  · exact p13MultiScaleRows_codeAudit_11 source target
  · exact p13MultiScaleRows_codeAudit_12 source target
  · exact p13MultiScaleRows_codeAudit_13 source target
  · exact p13MultiScaleRows_codeAudit_14 source target

theorem p13MultiScaleSafeCounts_audit (left right : Fin 15) :
    if 0 < left.1 ∧ 0 < right.1 ∧ left.1 + right.1 ≤ 14 then
      safeCount left.1 right.1 = profile.safeCount left.1 right.1
    else safeCount left.1 right.1 = 0 := by
  fin_cases left
  · exact p13MultiScaleSafeCounts_audit_00 right
  · exact p13MultiScaleSafeCounts_audit_01 right
  · exact p13MultiScaleSafeCounts_audit_02 right
  · exact p13MultiScaleSafeCounts_audit_03 right
  · exact p13MultiScaleSafeCounts_audit_04 right
  · exact p13MultiScaleSafeCounts_audit_05 right
  · exact p13MultiScaleSafeCounts_audit_06 right
  · exact p13MultiScaleSafeCounts_audit_07 right
  · exact p13MultiScaleSafeCounts_audit_08 right
  · exact p13MultiScaleSafeCounts_audit_09 right
  · exact p13MultiScaleSafeCounts_audit_10 right
  · exact p13MultiScaleSafeCounts_audit_11 right
  · exact p13MultiScaleSafeCounts_audit_12 right
  · exact p13MultiScaleSafeCounts_audit_13 right
  · exact p13MultiScaleSafeCounts_audit_14 right

theorem p13MultiScaleFlatCounts_audit (left right : Fin 15) :
    if 0 < left.1 ∧ 0 < right.1 ∧ left.1 + right.1 ≤ 14 then
      flatCount left.1 right.1 = profile.flatCount left.1 right.1
    else flatCount left.1 right.1 = 0 := by
  fin_cases left
  · exact p13MultiScaleFlatCounts_audit_00 right
  · exact p13MultiScaleFlatCounts_audit_01 right
  · exact p13MultiScaleFlatCounts_audit_02 right
  · exact p13MultiScaleFlatCounts_audit_03 right
  · exact p13MultiScaleFlatCounts_audit_04 right
  · exact p13MultiScaleFlatCounts_audit_05 right
  · exact p13MultiScaleFlatCounts_audit_06 right
  · exact p13MultiScaleFlatCounts_audit_07 right
  · exact p13MultiScaleFlatCounts_audit_08 right
  · exact p13MultiScaleFlatCounts_audit_09 right
  · exact p13MultiScaleFlatCounts_audit_10 right
  · exact p13MultiScaleFlatCounts_audit_11 right
  · exact p13MultiScaleFlatCounts_audit_12 right
  · exact p13MultiScaleFlatCounts_audit_13 right
  · exact p13MultiScaleFlatCounts_audit_14 right

end HypostructureErdos64EG.FiniteChecks.P13Barrier
