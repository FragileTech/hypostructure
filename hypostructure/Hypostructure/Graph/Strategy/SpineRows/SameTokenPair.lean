import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SameTokenPair

/-!
# G's same-token pattern pair, made exact (`[144]`, `[144a]`)

Type A rows (contracts: `Graph/Contracts/Spine/SameTokenPair.lean`).  No row
decides or splits anything.
- Right after the routing of `lem:same-token-bottleneck-routing` at `[144]`
  (`K .bottleneckRouting`), above the handoff decision, so every `[144a]`
  ledger carries them: the pattern supports of G's canonical routing and the
  exact swaps of its two readings.
- On `[144a]` (the handoff-fails arm, after `K .sameTokenPatternUnresolved`):
  the exact partition of the unresolved pair, with its region constraints;
  the one-sided region is empty at G.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[144]`, after the routing: the pattern supports of G's canonical
routing and the exact swaps of its two readings. -/
@[reducible] noncomputable def sameTokenPatternSupportsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sameTokenPatternSupports
    { Requires := [K .bottleneckRouting, K .sparseSurplusSurvivor, K .noProperBaseline,
        K .tightEndpoint]
      Produces := [K .sameTokenPatternSupports, K .sameTokenPatternSwap]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .sameTokenPatternSupports)
        ⟨Contracts.Spine.SameTokenPair.sameTokenPatternSupports_holds
          (inputs.get (K .bottleneckRouting)).down (inputs.get (K .sparseSurplusSurvivor)).down
          (inputs.get (K .noProperBaseline)).down⟩
      (.cons (key := K .sameTokenPatternSwap)
        ⟨Contracts.Spine.SameTokenPair.sameTokenPatternSwap_holds
          (inputs.get (K .bottleneckRouting)).down (inputs.get (K .sparseSurplusSurvivor)).down
          (inputs.get (K .tightEndpoint)).down⟩
      .nil))

/-- Node `[144a]`: the exact partition of G's unresolved pattern pair. -/
@[reducible] noncomputable def sameTokenPairPartitionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sameTokenPairPartition
    { Requires := [K .sameTokenPatternUnresolved, K .noProperBaseline, K .selection,
        K .cubicBaseline]
      Produces := [K .sameTokenPairPartition]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .sameTokenPairPartition)
        ⟨Contracts.Spine.SameTokenPair.sameTokenPairPartition_holds
          (inputs.get (K .sameTokenPatternUnresolved)).down
          (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .selection)).down.1
          (inputs.get (K .cubicBaseline)).down.2.1.2.1⟩
      .nil)

/-- Node `[144a]` (Lean improvement): the transplants of G's pattern supports into
`Z`, with the size equality, and their exact failure. -/
@[reducible] noncomputable def sameTokenTransplantRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sameTokenTransplant
    { Requires := [K .sameTokenPairPartition, K .noProperBaseline, K .selection,
        K .minDegreeBaseline]
      Produces := [K .sameTokenTransplantSize, K .sameTokenTransplantDeficit]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .sameTokenTransplantSize)
        ⟨Contracts.Spine.SameTokenPair.sameTokenTransplantSize_holds
          (inputs.get (K .sameTokenPairPartition)).down
          (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .selection)).down.1
          (fun H smaller base => (inputs.get (K .selection)).down.2.sizeMinimal H smaller base)⟩
      (.cons (key := K .sameTokenTransplantDeficit)
        ⟨Contracts.Spine.SameTokenPair.sameTokenTransplantDeficit_holds
          (inputs.get (K .sameTokenPairPartition)).down
          (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .selection)).down.1
          (fun H smaller base => (inputs.get (K .selection)).down.2.sizeMinimal H smaller base)
          (inputs.get (K .minDegreeBaseline)).down⟩
      .nil))

end Hypostructure.Graph.Strategy.Spine
