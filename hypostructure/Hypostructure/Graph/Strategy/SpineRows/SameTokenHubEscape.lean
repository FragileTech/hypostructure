import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SameTokenHubEscape

/-!
# Hubs escape to `Y` along the canonical port walks; the triangular sub-arm is empty
(`[144a]` exchange attack, Lean improvement)

Two Type A rows (contracts: `Graph/Contracts/Spine/SameTokenHubEscape.lean`).  No row decides
or splits anything.

* `sameTokenHubEscapeRow` (9852–9854), right after `sameTokenWalkWindowsRow` (node `[144]`,
  above the handoff decision): it reads only the canonical routing's existence
  (`K .sameTokenPatternSupports`) and G's global facts, so every `[144a]` ledger carries it.
* `sameTokenTriArmRow` (9855), on `[144a]`'s handoff-fails arm right after
  `K .sameTokenPairPartition`, the first key it needs (the pinned `X_p`, `X_q`, `Z` and the
  boundary-free configuration, `SameTokenSwap.sameTokenU2FreeWhole_holds`).
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[144]`, after the walk windows: the W0 escape (9852), the crossings (9853) and the
hub count (9854) at the canonical port walks. -/
@[reducible] noncomputable def sameTokenHubEscapeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sameTokenHubEscape
    { Requires := [K .sameTokenPatternSupports, K .selection, K .activeSurplusFamily,
        K .cubicBaseline, K .minDegreeBaseline, K .slackIndependent]
      Produces := [K .sameTokenW0Escape, K .sameTokenCrossingCount, K .sameTokenHubCount]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .sameTokenW0Escape)
        ⟨Contracts.Spine.SameTokenHubEscape.sameTokenW0Escape_holds
          (inputs.get (K .sameTokenPatternSupports)).down
          (inputs.get (K .selection)).down.1
          (inputs.get (K .activeSurplusFamily)).down
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .cubicBaseline)).down.2.1.2.1
          (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .slackIndependent)).down⟩
      (.cons (key := K .sameTokenCrossingCount)
        ⟨Contracts.Spine.SameTokenHubEscape.sameTokenCrossingCount_holds
          (inputs.get (K .sameTokenPatternSupports)).down
          (inputs.get (K .selection)).down.1
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .cubicBaseline)).down.2.1.2.1
          (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .slackIndependent)).down⟩
      (.cons (key := K .sameTokenHubCount)
        ⟨Contracts.Spine.SameTokenHubEscape.sameTokenHubCount_holds
          (inputs.get (K .sameTokenPatternSupports)).down
          (inputs.get (K .selection)).down.1
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .cubicBaseline)).down.2.1.2.1
          (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .slackIndependent)).down⟩
      .nil)))

/-- Node `[144a]`, after the partition: the triangular sub-arm W ∧ Tri ∧ EndEdgesFree is empty
at G (9855). -/
@[reducible] noncomputable def sameTokenTriArmRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sameTokenTriArmEmpty
    { Requires := [K .sameTokenPairPartition, K .noProperBaseline, K .selection,
        K .vertexDeletionComponents, K .minDegreeBaseline, K .cubicBaseline,
        K .slackIndependent, K .orderAboveScaleSquare, K .surplusAbove,
        K .ceilSqrtAboveScale]
      Produces := [K .sameTokenTriArmEmpty]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .sameTokenTriArmEmpty)
        ⟨Contracts.Spine.SameTokenHubEscape.sameTokenTriArmEmpty_holds
          (inputs.get (K .sameTokenPairPartition)).down
          (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .selection)).down.1
          (fun H smaller base => (inputs.get (K .selection)).down.2.sizeMinimal H smaller base)
          (inputs.get (K .vertexDeletionComponents)).down
          (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .cubicBaseline)).down.2.1.2.1
          (inputs.get (K .slackIndependent)).down
          (inputs.get (K .orderAboveScaleSquare)).down
          data.quadraticSafetyScale_le_twiceAdditive
          (inputs.get (K .surplusAbove)).down
          (inputs.get (K .ceilSqrtAboveScale)).down⟩
      .nil)

end Hypostructure.Graph.Strategy.Spine
