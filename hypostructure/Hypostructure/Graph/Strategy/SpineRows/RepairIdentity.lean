import Hypostructure.Graph.Strategy.SpineRows.Basic
import Hypostructure.Graph.Contracts.Spine.BranchD

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
at the delayed compensation components of the support of the certificate
node `[43]` routes (`branchCertificate?`): they are read from `K
.globalDelocalization`, and their internal degree bound from the residual's
baseline at the cubic threshold (`K .cubicBaseline`).

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
    { Requires := [K .globalDelocalization, K .cubicBaseline]
      Produces := [K .repairIdentity]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .repairIdentity)
        ⟨Contracts.Spine.repairIdentity_of_globalDelocalization data.toParameters
          inputs.current.object (inputs.get (K .globalDelocalization)).down
          inputs.current.baseline (inputs.get (K .cubicBaseline)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
