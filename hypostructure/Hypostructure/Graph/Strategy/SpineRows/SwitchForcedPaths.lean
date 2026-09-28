import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SwitchForcedPaths

/-!
# The forced paths and cycles of G's switches and vertex splits, at the entry

Type A rows (contracts: `Graph/Contracts/Spine/SwitchForcedPaths.lean`).  Each
row reads its prerequisites through `inputs.get` and publishes, at G's own
vertices, the path or cycle that G's minimality forces on an edge switch or a
vertex split.  No row decides or splits anything.  Each runs on the entry
prefix right after the last producer of the keys it reads, so every branch
below inherits its facts:
- after `[1]`--`[3]`'s baseline: the two-edge switch and the cross-vertex
  switch family;
- after `[9]`/`[10]` (the tight-endpoint law): the vertex split at every high
  centre;
- after `[6]`'s no arm (the return avoidance): the same-vertex switch.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Entry prefix, after `[1]`--`[3]`'s baseline: the two-edge switch of G and
the cross-vertex switch family (with the dyadic star). -/
@[reducible] noncomputable def entrySwitchPathsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.entrySwitchPaths
    { Requires := [K .selection, K .cubicBaseline, K .minDegreeBaseline]
      Produces := [K .twoSwitchForcedPath, K .crossSwitchFamily]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .twoSwitchForcedPath)
        ⟨Contracts.Spine.SwitchForcedPaths.twoSwitchForcedPath_holds
          (inputs.get (K .selection)).down (inputs.get (K .minDegreeBaseline)).down⟩
      (.cons (key := K .crossSwitchFamily)
        ⟨Contracts.Spine.SwitchForcedPaths.crossSwitchFamily_holds
          (inputs.get (K .selection)).down (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .cubicBaseline)).down.2.1.2.1⟩
      .nil))

/-- Entry prefix, after `[9]`/`[10]`: the vertex split of G at every high
centre (the tight-endpoint law makes `G[N(h)]` a matching). -/
@[reducible] noncomputable def highCentreSplitForcedRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.highCentreSplitForced
    { Requires := [K .selection, K .cubicBaseline, K .minDegreeBaseline, K .tightEndpoint]
      Produces := [K .highCentreSplitForced]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .highCentreSplitForced)
        ⟨Contracts.Spine.SwitchForcedPaths.highCentreSplitForced_holds
          (inputs.get (K .selection)).down (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .cubicBaseline)).down.2.1.1
          (inputs.get (K .tightEndpoint)).down⟩
      .nil)

/-- Entry prefix, on `[6]`'s no arm (the return avoidance): the same-vertex
switch of G, with the exact split of its forced path. -/
@[reducible] noncomputable def sameVertexSwitchForcedPathRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sameVertexSwitchForcedPath
    { Requires := [K .selection, K .minDegreeBaseline, K .returnAvoidance]
      Produces := [K .sameVertexSwitchForcedPath]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .sameVertexSwitchForcedPath)
        ⟨Contracts.Spine.SwitchForcedPaths.sameVertexSwitchForcedPath_holds
          (inputs.get (K .selection)).down (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .returnAvoidance)).down⟩
      .nil)

end Hypostructure.Graph.Strategy.Spine
