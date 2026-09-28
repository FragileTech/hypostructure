import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.CycleCounting

/-!
# The cycles through the vertices of G, each published at the earliest point

Type A rows over `Graph/Contracts/Spine/CycleCounting.lean`.  Each row reads
its prerequisites through `inputs.get` and publishes facts of G; no row decides
or splits anything.  All four run on the entry prefix
(`Assembly/Entry.lean`), right after the last producer of the keys they read,
so every branch below carries their facts:
- after the presentation laws (reads `K .selection`, `K .cubicBaseline`);
- after `[1]`--`[3]`'s baseline;
- after `[8]` and `lem:bridgeless` (next to the single-boundary shape);
- after `[9]`/`[10]` (reads `K .slackIndependent`).
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Entry prefix, right after the presentation laws: at every vertex `h` of G,
`G[N(h)]` is a matching with its nonadjacent pair counts, and the star and
meeting constraints on two paths of `G − h` to distinct neighbours of `h`. -/
@[reducible] noncomputable def cycleNeighbourhoodRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.cycleNeighbourhood
    { Requires := [K .selection, K .cubicBaseline]
      Produces := [K .neighbourhoodPairCount, K .starCycleConstraint,
        K .meetingCycleConstraint]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .neighbourhoodPairCount)
        ⟨Contracts.Spine.CycleCounting.neighbourhoodPairCount_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .cubicBaseline)).down.2.1.1⟩
      (.cons (key := K .starCycleConstraint)
        ⟨Contracts.Spine.CycleCounting.starCycleConstraint_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .cubicBaseline)).down.2.1.2.1⟩
      (.cons (key := K .meetingCycleConstraint)
        ⟨Contracts.Spine.CycleCounting.meetingCycleConstraint_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .cubicBaseline)).down.2.1.2.1⟩
      .nil)))

/-- Entry prefix, right after `[1]`--`[3]`'s baseline: the pair sums
`Σ_{d_h ≠ δ} C(d_h, 2)` against the surplus `σ`. -/
@[reducible] noncomputable def highDegreePairSumRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.highDegreePairSum
    { Requires := [K .cubicBaseline, K .minDegreeBaseline]
      Produces := [K .highDegreePairSum]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .highDegreePairSum)
        ⟨Contracts.Spine.CycleCounting.highDegreePairSum_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down⟩
      .nil)

/-- Entry prefix, after `[8]` and `lem:bridgeless`: at every vertex `h` of G,
`G − h` connected or `d_h` even with two neighbours of `h` per component; the
count of cycles through `h`; the block paths at the cut vertices. -/
@[reducible] noncomputable def cutVertexCyclesRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.cutVertexCycles
    { Requires := [K .selection, K .cubicBaseline, K .minDegreeBaseline, K .noProperBaseline,
        K .bridgeless]
      Produces := [K .vertexDeletionComponents, K .cyclesThroughVertex,
        K .cutVertexBlockPaths]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .vertexDeletionComponents)
        ⟨Contracts.Spine.CycleCounting.vertexDeletionComponents_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .bridgeless)).down⟩
      (.cons (key := K .cyclesThroughVertex)
        ⟨Contracts.Spine.CycleCounting.cyclesThroughVertex_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .bridgeless)).down⟩
      (.cons (key := K .cutVertexBlockPaths)
        ⟨Contracts.Spine.CycleCounting.cutVertexBlockPaths_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .bridgeless)).down (inputs.get (K .selection)).down.1 (inputs.get (K .cubicBaseline)).down.2.1.2.1⟩
      .nil)))

/-- Entry prefix, after `[9]`/`[10]`: the double count of the cycles of G at
its (independent) high vertices. -/
@[reducible] noncomputable def cycleDoubleCountRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.cycleDoubleCount
    { Requires := [K .cubicBaseline, K .minDegreeBaseline, K .noProperBaseline, K .bridgeless,
        K .slackIndependent]
      Produces := [K .cycleDoubleCount]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .cycleDoubleCount)
        ⟨Contracts.Spine.CycleCounting.cycleDoubleCount_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .bridgeless)).down (inputs.get (K .slackIndependent)).down⟩
      .nil)

end Hypostructure.Graph.Strategy.Spine
