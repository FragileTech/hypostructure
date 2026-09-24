import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Node `[57]` = `[173]`: the exact collision test

`lem:exact-collision-test`.  Node `[56]`'s collision is an inequality of the
current object — with the actual surpluses, the actual hot and cold window
counts, and the exact skeleton budget — and node `[173]` decides it on the
object: `def⁺(R) − σ_R < |R|/s` at every maximal packing (`NegativeNetCharge`),
which is exactly `K .netChargeCap`.  Its yes arm continues at `[58]`; its no arm
is the absorbed-germ residual `[174]` (`K .exactCollisionFails`).  No condition
on `n` is used (`rem:no-sufficient-order`): the sufficient-order reading of
node `[57]` and the cap row that consumed it are gone. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def exactCollisionDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    (capFresh : K .netChargeCap ∉ known)
    (failsFresh : K .exactCollisionFails ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .netChargeCap) (K .exactCollisionFails) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .netChargeCap) (K .exactCollisionFails)
    `Hypostructure.Graph.Strategy.Spine.exactCollisionDichotomy
    (by
      classical
      exact if holds : ∀ packing : Finset (Finset current.object.Vertex),
          current.object.IsWindowPacking data.windowOrder packing →
            packing.card = current.object.windowPackingNumber data.windowOrder →
              current.object.NegativeNetCharge (current.object.remainderSupport packing)
                data.threshold data.dischargeScale then
        .inl ⟨holds⟩
      else
        .inr ⟨by
          push_neg at holds
          obtain ⟨packing, valid, cardinality, notNegative⟩ := holds
          exact ⟨packing, valid, cardinality,
            (Graph.FiniteObject.not_negativeNetCharge_iff current.object _ _ _).1
              notNegative⟩⟩)
    capFresh failsFresh

end Hypostructure.Graph.Strategy.Spine
