import Hypostructure.Graph.Strategy.SpineRows.Basic

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

/-! ### Nodes `[44]` and `[45]`: the repair identity and the global barrier

`[44]` is `lem:smearing-support-repair`: a delayed compensation component with
`p` boundary leaves, `s` internal vertices, cycle rank `β` and surplus `σ`
satisfies `s = p − 2 + 2β − σ`.  The manuscript proves it from the handshake
identity and the cycle-rank formula.  The row below performs that derivation
inside its atomic executor for every repair component embedded in the active
support.  Node `[43]` remains in the literal ledger ancestry but is not copied
or falsely declared as an arithmetic prerequisite; the proof does not appeal
to a detached universal result.

`[45]` is the barrier `lem:no-silent-global-smearing` raises against a
whole-graph dependence: the closed clause of `def:admissible-rank-quotient`
supplies a strictly smaller admissible closed representative.  The target-defect
case is excluded by the inherited target-completeness, the exact-label case is
excluded by the inherited rank reduction, and node `[43]`'s coverage proof
places the quotient in the closed rather than proper-support clause. -/
@[reducible] noncomputable def repairIdentityRow
    (data : Data.{u}) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.repairIdentity
    (sourceFreeManifest (K .repairIdentity))
    (fun inputs =>
      .cons (key := K .repairIdentity)
        (show Value BranchState Presentation presentation data
            .repairIdentity inputs.current from
          ⟨by
            dsimp only [Holds]
            intro component _componentOnActiveSupport
            have handshake :
                (3 : Int) * component.internal.card + component.surplus +
                    component.boundary.card =
                  2 * component.object.edgeCount := by
              exact_mod_cast component.handshake
            have rank := component.cycleRank_cast
            rw [component.vertexCard_eq] at rank
            push_cast at rank
            linarith⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine
