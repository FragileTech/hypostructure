import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.LocalRigidity

/-!
# Local rigidity of G, each fact published at the earliest point

Type A rows over `Graph/Contracts/Spine/LocalRigidity.lean`.  Each row reads
its prerequisites through `inputs.get` and publishes facts of G; no row decides
or splits anything.  Both run on the entry prefix (`Assembly/Entry.lean`):
- the length-3 fan and the chain `3, 3, 3`, right after the presentation laws
  (reads `K .selection`, `K .cubicBaseline`), next to the star and meeting
  constraints;
- the window positions and the attachment gaps, right after the canonical
  packing `P₀` (reads `K .selection`, `K .cubicBaseline`).
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Entry prefix, right after the presentation laws: the length-3 fan at
every vertex of G and the chain `3, 3, 3`. -/
@[reducible] noncomputable def threeRouteRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.threeRoute
    { Requires := [K .selection, K .cubicBaseline]
      Produces := [K .threeRouteFan, K .threeRouteChain]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .threeRouteFan)
        ⟨Contracts.Spine.LocalRigidity.threeRouteFan_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .cubicBaseline)).down.2.1.2.1⟩
      (.cons (key := K .threeRouteChain)
        ⟨Contracts.Spine.LocalRigidity.threeRouteChain_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .cubicBaseline)).down.2.1.2.1⟩
      .nil))

/-- Entry prefix, right after the canonical packing `P₀`: the placements and
stub counts of its windows, and the attachment gaps (legal labels, `C₁`
safety, the cross-window gap rule, no ladder). -/
@[reducible] noncomputable def windowRigidityRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.windowRigidity
    { Requires := [K .selection, K .cubicBaseline]
      Produces := [K .windowPositionStubs, K .windowAttachmentGap]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .windowPositionStubs)
        ⟨Contracts.Spine.LocalRigidity.windowPositionStubs_holds (object := inputs.current.object)⟩
      (.cons (key := K .windowAttachmentGap)
        ⟨Contracts.Spine.LocalRigidity.windowAttachmentGap_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .cubicBaseline)).down.2.1.2.1⟩
      .nil))

end Hypostructure.Graph.Strategy.Spine
