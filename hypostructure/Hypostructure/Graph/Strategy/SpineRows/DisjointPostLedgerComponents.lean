import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Certificate

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Nodes `[74]`/`[82]`, the B2 refinement B2(a)--(d) on the B2-success arm. -/
@[reducible] noncomputable def disjointPostLedgerComponentsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.disjointPostLedgerComponents
    { Requires := [K .typeBB2Choice, K .selection, K .uncompressible, K .remainderNormalized]
      Produces := [K .typeBDisjointLedger]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBDisjointLedger)
        ⟨Contracts.TypeB.typeBDisjointLedger (inputs.get (K .selection)).down.1
          (fun vertex => le_trans inputs.current.baseline
            (inputs.current.object.minDegree_le_degree vertex))
          (inputs.get (K .uncompressible)).down (inputs.get (K .remainderNormalized)).down
          (inputs.get (K .typeBB2Choice)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
