import Mathlib

namespace Hypostructure.Quarantine.PaperRepairs.EntropyCapAllCold
/-! Evidence (reference only, not built) for `entropyCapBound_allCold` (PAPER-ERROR [54] tex:9921).

The ledger facts available at `[54]` constrain the four quantities the
statement mentions only through the following relations (all at `P₀`):
* `RS ≤ B`                      -- `RemainderGlue.remainderStateCount_le_skeletonBudget`
* `1 ≤ B`                       -- `skeletonBudget_pos`
* `B < RS * 2^(cr)`             -- the all-cold arm of `[22]`: `¬ WindowFamilyRealized ∅`
                                   read at `stateOf := id` (`K .skeletonDominates`, `.1`)
* `F ≤ cr`                      -- node `[48]` (`forcedObstructionBits_le_cost`)
* `N ≤ RS^d` (`N = n^|R|`)      -- node `[51]`; `[52]` is the same inequality on this arm
* `B < RS * 2^F`                -- the active arm of `[53]` (the closure's other input)
where `RS = remainderStates R₀`, `B = skeletonBudget`, `cr = c_Ω·r_Ω(R₀)`,
`F = forcedObstructionBits`.  Both the claim `RS * 2^F ≤ B` and its negation
are consistent with every one of these relations except the last (which is the
arm being closed), so neither is a consequence of them. -/

abbrev Hyps (RS B cr F N d : Nat) : Prop :=
  RS ≤ B ∧ 1 ≤ B ∧ B < RS * 2 ^ cr ∧ F ≤ cr ∧ N ≤ RS ^ d

-- the claim holds in a model of the hypotheses
example : ∃ RS B cr F N d, Hyps RS B cr F N d ∧ RS * 2 ^ F ≤ B :=
  ⟨2, 5, 3, 1, 1, 1, by unfold Hyps; decide, by decide⟩

-- its negation holds in a model of the hypotheses
example : ∃ RS B cr F N d, Hyps RS B cr F N d ∧ ¬ RS * 2 ^ F ≤ B :=
  ⟨2, 5, 3, 3, 1, 1, by unfold Hyps; decide, by decide⟩

-- with the active arm of [53] added, the claim is exactly what closes it
example (RS B F : Nat) (active : B < RS * 2 ^ F) (claim : RS * 2 ^ F ≤ B) : False :=
  absurd claim (Nat.not_le.mpr active)

end Hypostructure.Quarantine.PaperRepairs.EntropyCapAllCold
