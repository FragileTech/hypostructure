import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.BlockedFailureG
import Hypostructure.Graph.Contracts.Spine.BlockedPassing
import Hypostructure.Graph.Contracts.Spine.BlockedOverlapG

/-!
# Node `[172a]`: G's own record at the failure of `lem:scale-additivity`

A Type A row on the failure arm of node `[170]` (`Strategy/BlockedCompressionRows.lean`).  It
reads `K .blockedClassMember` (G's skeleton is a member of `𝓑(𝒫)`), the retained failure
`K .blockedBarrierOverlap` and the presentation laws `K .cubicBaseline`, and publishes G's own
facts at the failing coordinate's class: G's own record, the aggregate failure quantified, and the
prefix compression of the blocked class.  It decides and splits nothing.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Node `[172a]`**, on the failure arm of `[170]`: G's own record, the aggregate failure
quantified, and the prefix compression of `𝓑(𝒫)`. -/
@[reducible] noncomputable def blockedFailureGRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.blockedFailureG
    { Requires := [K .blockedClassMember, K .blockedBarrierOverlap, K .cubicBaseline]
      Produces := [K .blockedOwnRecord, K .blockedFailureSlack, K .blockedPrefixCompression,
        K .blockedFailingSetCarries, K .blockedOverlapSupport]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .blockedOwnRecord)
        ⟨match (inputs.get (K .cubicBaseline)).down.2.2.2 with
          | ⟨_, _, _, _, labelMem, labelInjective, labelSurjective, leftSemantic,
              rightSemantic, sumSemantic⟩ =>
            Contracts.Spine.blockedOwnRecord_holds data.toParameters inputs.current.object
              (inputs.get (K .cubicBaseline)).down.2.1.2.1
              (inputs.get (K .cubicBaseline)).down.1.2.2.1
              data.windowBarrierLabel labelMem labelInjective labelSurjective
              leftSemantic rightSemantic sumSemantic
              (inputs.get (K .blockedClassMember)).down⟩
      (.cons (key := K .blockedFailureSlack)
        ⟨Contracts.Spine.blockedFailureSlack_holds data.toParameters inputs.current.object
          (inputs.get (K .blockedClassMember)).down
          (inputs.get (K .blockedBarrierOverlap)).down⟩
      (.cons (key := K .blockedPrefixCompression)
        ⟨Contracts.Spine.blockedPrefixCompression_holds data.toParameters
          inputs.current.object⟩
      (.cons (key := K .blockedFailingSetCarries)
        ⟨Contracts.Spine.blockedFailingSetCarries_holds data.toParameters
          inputs.current.object⟩
      (.cons (key := K .blockedOverlapSupport)
        ⟨Contracts.Spine.blockedOverlapSupport_holds data.toParameters inputs.current.object
          (inputs.get (K .cubicBaseline)).down.2.1.2.1
          (inputs.get (K .blockedClassMember)).down⟩
      .nil)))))

end Hypostructure.Graph.Strategy.Spine
