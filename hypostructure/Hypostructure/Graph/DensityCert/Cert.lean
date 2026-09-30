import Hypostructure.Graph.DensityCert.CertShard00
import Hypostructure.Graph.DensityCert.CertShard01
import Hypostructure.Graph.DensityCert.CertShard02
import Hypostructure.Graph.DensityCert.CertShard03
import Hypostructure.Graph.DensityCert.CertShard04
import Hypostructure.Graph.DensityCert.CertShard05
import Hypostructure.Graph.DensityCert.CertShard06
import Hypostructure.Graph.DensityCert.CertShard07
import Hypostructure.Graph.DensityCert.CertShard08
import Hypostructure.Graph.DensityCert.CertShard09
import Hypostructure.Graph.DensityCert.CertShard10
import Hypostructure.Graph.DensityCert.CertShard11
import Hypostructure.Graph.DensityCert.CertShard12
import Hypostructure.Graph.DensityCert.CertShard13
import Hypostructure.Graph.DensityCert.CertShard14
import Hypostructure.Graph.DensityCert.CertShard15

/-!
# Density certificate

`Lcert` (`K₂` and the 5519 two-connected admissible blocks, see `Data.lean`) is
closed under admissible ear extensions with at most 11 new vertices, contains `K₂`,
and satisfies the block-profile inequalities of the tree DP.  The per-member checks
are the `native_decide` shards `CertShard00` – `CertShard15`.
-/

namespace Hypostructure.Graph.DensityCert

open CertCheck CertSearch CertShards

private theorem LArr_size : LArr.size = 5520 := by native_decide

private theorem all_members (i : ℕ) (hi : i < 5520) :
    ClosureBody LArr.toList (LArr.getD i CG.K2) ∧ DPBody (LArr.getD i CG.K2) := by
  by_cases h0 : i < 345
  · exact rangeOK_sound range_0 i (by omega) h0
  by_cases h1 : i < 690
  · exact rangeOK_sound range_345 i (by omega) h1
  by_cases h2 : i < 1035
  · exact rangeOK_sound range_690 i (by omega) h2
  by_cases h3 : i < 1380
  · exact rangeOK_sound range_1035 i (by omega) h3
  by_cases h4 : i < 1725
  · exact rangeOK_sound range_1380 i (by omega) h4
  by_cases h5 : i < 2070
  · exact rangeOK_sound range_1725 i (by omega) h5
  by_cases h6 : i < 2415
  · exact rangeOK_sound range_2070 i (by omega) h6
  by_cases h7 : i < 2760
  · exact rangeOK_sound range_2415 i (by omega) h7
  by_cases h8 : i < 3105
  · exact rangeOK_sound range_2760 i (by omega) h8
  by_cases h9 : i < 3450
  · exact rangeOK_sound range_3105 i (by omega) h9
  by_cases h10 : i < 3795
  · exact rangeOK_sound range_3450 i (by omega) h10
  by_cases h11 : i < 4140
  · exact rangeOK_sound range_3795 i (by omega) h11
  by_cases h12 : i < 4485
  · exact rangeOK_sound range_4140 i (by omega) h12
  by_cases h13 : i < 4830
  · exact rangeOK_sound range_4485 i (by omega) h13
  by_cases h14 : i < 5175
  · exact rangeOK_sound range_4830 i (by omega) h14
  exact rangeOK_sound range_5175 i (by omega) hi

private theorem exists_index {M : CG} (hM : M ∈ Lcert) : ∃ i < 5520, LArr.getD i CG.K2 = M := by
  unfold Lcert at hM
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hM
  rw [Array.length_toList] at hi
  refine ⟨i, LArr_size ▸ hi, ?_⟩
  simp [Array.getD_eq_getD_getElem?, hi]

theorem closure_cert : ClosureCert Lcert := fun M hM => by
  obtain ⟨i, hi, rfl⟩ := exists_index hM
  exact (all_members i hi).1

theorem dp_cert : DPCert Lcert := (dpCert_iff Lcert).2 fun M hM => by
  obtain ⟨i, hi, rfl⟩ := exists_index hM
  exact (all_members i hi).2

end Hypostructure.Graph.DensityCert
