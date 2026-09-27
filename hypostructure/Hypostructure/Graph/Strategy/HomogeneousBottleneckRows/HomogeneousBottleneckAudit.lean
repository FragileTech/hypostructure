import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic
import Hypostructure.Graph.Contracts.SurplusPair.OverloadClass

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Nodes `[140]`, `[142]`, `[143]`: the geometric audits

One audit argument (`homogeneousBottleneckPattern_of_class`), run
on G's canonical overloading token, whose class `[139]`/`[141]` decided: its role
fibre carries a role-homogeneous same-token `L_geom`-matching or `L_geom`-star
with every declared same-root connector configuration.  This is the only
derivation of the bottleneck pattern consumed by `[144]`. -/

/-- Node `[140]`: the window-incidence geometric audit. -/
@[reducible] noncomputable def windowBottleneckAuditRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.windowBottleneckAudit
    { Requires := [K .windowClassOverload, K .capacityTokenLedger,
        K .cubicBaseline]
      Produces := [K .homogeneousBottleneckPattern]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .homogeneousBottleneckPattern)
        ⟨Graph.Contracts.SurplusPair.homogeneousBottleneckPattern_of_class
          (inputs.get (K .windowClassOverload)).down
          (inputs.get (K .capacityTokenLedger)).down
          (inputs.get (K .cubicBaseline)).down.2.2.1.2.2.1⟩
        .nil)

/-- Node `[142]`: the remainder-surplus geometric audit. -/
@[reducible] noncomputable def remainderBottleneckAuditRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.remainderBottleneckAudit
    { Requires := [K .remainderClassOverload, K .capacityTokenLedger,
        K .cubicBaseline]
      Produces := [K .homogeneousBottleneckPattern]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .homogeneousBottleneckPattern)
        ⟨Graph.Contracts.SurplusPair.homogeneousBottleneckPattern_of_class
          (inputs.get (K .remainderClassOverload)).down
          (inputs.get (K .capacityTokenLedger)).down
          (inputs.get (K .cubicBaseline)).down.2.2.1.2.2.1⟩
        .nil)

/-- Node `[143]`: the primitive blocker-support geometric audit. -/
@[reducible] noncomputable def primitiveBottleneckAuditRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.primitiveBottleneckAudit
    { Requires := [K .primitiveClassOverload, K .capacityTokenLedger,
        K .cubicBaseline]
      Produces := [K .homogeneousBottleneckPattern]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .homogeneousBottleneckPattern)
        ⟨Graph.Contracts.SurplusPair.homogeneousBottleneckPattern_of_class
          (inputs.get (K .primitiveClassOverload)).down
          (inputs.get (K .capacityTokenLedger)).down
          (inputs.get (K .cubicBaseline)).down.2.2.1.2.2.1⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
