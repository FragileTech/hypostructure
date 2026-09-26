import Hypostructure.Graph.Statements.SurplusPair

/-!
# Contract lemma: the blocker arm of `[132]`

`lem:sparse-pair-dependence-exit`, blocker arm: when no sparse surplus exit
settles the dependence of the blocked pair family of `[130]`, its recorded
blocker set is nonempty at some scheduled pair, which therefore has the
canonical blocker `Φ_can(π) = min_≺ Blk(π)` of `def:canonical-blocker-ledger`.
-/

namespace Hypostructure.Graph.Contracts.SurplusPair

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

theorem canonicalBlockerRoute_of_noExit
    (noExit : BlockedPairNoExitStatement data object)
    (dependent : DependentPairFamilyStatement data object) :
    CanonicalBlockerRouteStatement data object := by
  classical
  obtain ⟨active, certificate⟩ := dependent
  let pairs := object.portPairSchedule data.threshold
  let recorded := Graph.recordSparsePairDEBlockers
    (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
    (LengthOK := data.LengthOK) (Graph.pairResponseActivation active) pairs
  obtain ⟨pair, pairMem, blocked⟩ :=
    Graph.recordedSparsePairDEBlocker_nonempty
      (Graph.pairResponseActivation active) pairs certificate
  obtain ⟨blocker, canonical⟩ := Option.isSome_iff_exists.mp
    (Graph.FiniteObject.isSome_canonicalBlocker recorded blocked)
  exact ⟨noExit, active, certificate, pair, pairMem, blocked, blocker,
    canonical⟩

end Hypostructure.Graph.Contracts.SurplusPair
