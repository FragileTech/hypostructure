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

/-- Node `[74]`, the B2 refinement B2(a)--(d) on the B2 yes arm of `[72]`: the
B2 fact at the Type B support makes it B2-paid. -/
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

/-- Node `[82]`, `lem:typeB-exclusion` Step 1 and `prop:typeB-bridge-reduction`
on the `[81]` yes arm: every assigned centre with `c ≤ 1` has a
certificate-closed marked fan, or the support is B2-paid and its remaining core
carries the whole deficit. -/
@[reducible] noncomputable def typeBDegreeFourClosedRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBDegreeFourClosed
    { Requires := [K .typeBDegreeFourLedger, K .typeBFanDegreeFourCentres,
        K .cubicBaseline, K .selection, K .uncompressible, K .remainderNormalized]
      Produces := [K .typeBDegreeFourClosed]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBDegreeFourClosed)
        ⟨Contracts.TypeB.typeBDegreeFourClosed (inputs.get (K .selection)).down.1
          (fun vertex => le_trans inputs.current.baseline
            (inputs.current.object.minDegree_le_degree vertex))
          (inputs.get (K .uncompressible)).down (inputs.get (K .remainderNormalized)).down
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .cubicBaseline)).down.1.2.1
          (inputs.get (K .typeBFanDegreeFourCentres)).down
          (inputs.get (K .typeBDegreeFourLedger)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
