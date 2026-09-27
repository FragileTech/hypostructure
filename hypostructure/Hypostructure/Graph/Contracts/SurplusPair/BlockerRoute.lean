import Hypostructure.Graph.Statements.SurplusPair

/-!
# Contract lemma: the blocker arm of `[132]`

Node `[132]`, blocker arm: when no sparse surplus exit occurs, the blocked pair
`π ∈ Π_blk` of `[130]` (nonempty recorded blocker set over the six clauses of
`def:surplus-blockers`) has the canonical blocker `Φ_can(π) = min_≺ 𝖡𝗅𝗄(π)` of
`def:canonical-blocker-ledger`.
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
  obtain ⟨activation, selected, certificate⟩ := dependent
  let pairs := object.portPairSchedule data.threshold
  let recorded := Graph.recordSparsePairDEBlockers
    (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
    (LengthOK := data.LengthOK) activation pairs
  obtain ⟨pair, pairMem, blocked⟩ := id certificate
  obtain ⟨blocker, canonical⟩ := Option.isSome_iff_exists.mp
    (Graph.FiniteObject.isSome_canonicalBlocker recorded blocked)
  exact ⟨noExit, activation, selected, certificate, pair, pairMem, blocked,
    blocker, canonical⟩

end Hypostructure.Graph.Contracts.SurplusPair
