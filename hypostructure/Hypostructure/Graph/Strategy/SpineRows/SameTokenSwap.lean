import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SameTokenSwap
import Hypostructure.Graph.Contracts.Spine.SameTokenSeedCover

/-!
# G's pattern pair, tested at G (`[144a]`, G audit S144a)

One Type A row (contracts: `Graph/Contracts/Spine/SameTokenSwap.lean`).  No row
decides or splits anything.  On `[144a]`'s handoff-fails arm, after
`K .sameTokenPairPartition`: the entry test decided at G, the exact readings,
the rerouted swaps in both directions with their exact failure, and the
boundary-free configuration.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[144a]` (G audit S144a): the pair tested at G. -/
@[reducible] noncomputable def sameTokenSwapRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sameTokenSwap
    { Requires := [K .sameTokenPairPartition, K .noProperBaseline, K .selection,
        K .minDegreeBaseline, K .vertexDeletionComponents, K .cubicBaseline,
        K .activeSurplusFamily, K .hubCountBound, K .slackIndependent]
      Produces := [K .sameTokenUnresolvedDecided, K .sameTokenReadingsExact, K .sameTokenSwap,
        K .sameTokenSwapExact, K .sameTokenU2FreeWhole, K .sameTokenSeedCover,
        K .sameTokenPathInteractions]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .sameTokenUnresolvedDecided)
        ⟨Contracts.Spine.SameTokenSwap.sameTokenUnresolvedDecided_holds
          (inputs.get (K .sameTokenPairPartition)).down
          (inputs.get (K .selection)).down.1⟩
      (.cons (key := K .sameTokenReadingsExact)
        ⟨Contracts.Spine.SameTokenSwap.sameTokenReadingsExact_holds
          (inputs.get (K .sameTokenPairPartition)).down
          (inputs.get (K .selection)).down.1
          (fun H smaller base => (inputs.get (K .selection)).down.2.sizeMinimal H smaller base)⟩
      (.cons (key := K .sameTokenSwap)
        ⟨Contracts.Spine.SameTokenSwap.sameTokenSwap_holds
          (inputs.get (K .sameTokenPairPartition)).down
          (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .selection)).down.1
          (fun H smaller base => (inputs.get (K .selection)).down.2.sizeMinimal H smaller base)⟩
      (.cons (key := K .sameTokenSwapExact)
        ⟨Contracts.Spine.SameTokenSwap.sameTokenSwapExact_holds
          (inputs.get (K .sameTokenPairPartition)).down
          (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .selection)).down.1
          (fun H smaller base => (inputs.get (K .selection)).down.2.sizeMinimal H smaller base)
          (inputs.get (K .minDegreeBaseline)).down⟩
      (.cons (key := K .sameTokenU2FreeWhole)
        ⟨Contracts.Spine.SameTokenSwap.sameTokenU2FreeWhole_holds
          (inputs.get (K .sameTokenPairPartition)).down
          (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .selection)).down.1
          (fun H smaller base => (inputs.get (K .selection)).down.2.sizeMinimal H smaller base)
          (inputs.get (K .vertexDeletionComponents)).down
          (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .cubicBaseline)).down.1.1⟩
      (.cons (key := K .sameTokenSeedCover)
        ⟨Contracts.Spine.SameTokenSeedCover.sameTokenSeedCover_holds
          (inputs.get (K .sameTokenPairPartition)).down
          (inputs.get (K .selection)).down.1
          (inputs.get (K .activeSurplusFamily)).down
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .hubCountBound)).down⟩
      (.cons (key := K .sameTokenPathInteractions)
        ⟨Contracts.Spine.SameTokenSeedCover.sameTokenPathInteractions_holds
          (inputs.get (K .sameTokenPairPartition)).down
          (inputs.get (K .selection)).down.1
          (inputs.get (K .activeSurplusFamily)).down
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .slackIndependent)).down⟩
      .nil)))))))

end Hypostructure.Graph.Strategy.Spine
