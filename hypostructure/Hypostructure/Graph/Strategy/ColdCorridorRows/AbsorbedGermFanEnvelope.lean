import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Entry
import Hypostructure.Graph.Contracts.Spine.ColdAbsorbedEmpty

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Node `[175]`, read at `[177]`: selected corridor meets a high-degree
vertex?**  The decision reads the node-`[177]` fan data
(`K .absorbedGermFanData`) and splits at `G`'s one canonical object
`canonicalTypeBAbsorbedHalfEdge`: some selected half-edge lies outside node
`[153]`'s subcubic candidates (its corridor meets a high vertex, and it enters
Type B at `[65]`), or every selected corridor is subcubic. -/
noncomputable def typeBAbsorbedHalfEdgeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .absorbedGermFanData) known]
    (outsideFresh : K .typeBAbsorbedHalfEdge ∉ known)
    (absentFresh : K .typeBAbsorbedHalfEdgeAbsent ∉ known) :
    Decision (K .typeBAbsorbedHalfEdge) (K .typeBAbsorbedHalfEdgeAbsent) previous :=
  Decision.run previous (K .typeBAbsorbedHalfEdge) (K .typeBAbsorbedHalfEdgeAbsent)
    `Hypostructure.Graph.Strategy.Spine.typeBAbsorbedHalfEdgeDichotomy
    (Classical.choice (show Nonempty
        ((K .typeBAbsorbedHalfEdge).At current ⊕
          (K .typeBAbsorbedHalfEdgeAbsent).At current) from by
      rcases Contracts.TypeB.typeBAbsorbedHalfEdge_split
          (ExactLedger.get previous (K .absorbedGermFanData)).down with holds | holds
      · exact ⟨.inl ⟨holds⟩⟩
      · exact ⟨.inr ⟨holds⟩⟩))
    outsideFresh absentFresh

/-- **Node `[177]`, `lem:absorbed-germ-fan-data`: every half-edge the bounded arm
of `[153]` discards is charged to the Type B ledger.**  Every selected
half-edge outside node `[153]`'s subcubic candidates whose canonical absorbed
handoff `(z_ε, Y_ε)` is defined has its own pinned absorbed Type B support
`(Y_ε, {z_ε} ∪ centres(Y_ε))`, and that support's negative part is charged to
its assigned surplus (`lem:typeB-bridge-deficit-bound`); the half-edges without
a counted core are charged by `absorbedF4ChargeRow`. -/
@[reducible] noncomputable def typeBAbsorbedChargeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBAbsorbedCharge
    { Requires := [K .cubicBaseline]
      Produces := [K .typeBAbsorbedCharge]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBAbsorbedCharge)
        ⟨Contracts.TypeB.typeBAbsorbedCharge
          (fun vertex => le_trans inputs.current.baseline
            (inputs.current.object.minDegree_le_degree vertex))
          (inputs.get (K .cubicBaseline)).down.2.1.2.2.2.2⟩
        .nil)

/-- **Node `[177]`: does a counted remainder core exist at the heavy centre?**
The decision reads the `[175]` yes arm (`K .typeBAbsorbedHalfEdge`) and splits
at `G`'s one canonical absorbed half-edge `ε`: its canonical absorbed handoff
`(z, Y)` is defined (a counted core `Y ⊆ R(P₀)` exists at `z`,
`Contracts.TypeB.canonicalAbsorbedHandoff_isSome_iff_core`) or it is not. -/
noncomputable def absorbedHandoffCoreDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .typeBAbsorbedHalfEdge) known]
    (coreFresh : K .absorbedHandoffCore ∉ known)
    (absentFresh : K .absorbedHandoffCoreAbsent ∉ known) :
    Decision (K .absorbedHandoffCore) (K .absorbedHandoffCoreAbsent) previous :=
  Decision.run previous (K .absorbedHandoffCore) (K .absorbedHandoffCoreAbsent)
    `Hypostructure.Graph.Strategy.Spine.absorbedHandoffCoreDichotomy
    (Classical.choice (show Nonempty
        ((K .absorbedHandoffCore).At current ⊕
          (K .absorbedHandoffCoreAbsent).At current) from by
      rcases Contracts.TypeB.absorbedHandoffCore_split
          (ExactLedger.get previous (K .typeBAbsorbedHalfEdge)).down with holds | holds
      · exact ⟨.inl ⟨holds⟩⟩
      · exact ⟨.inr ⟨holds⟩⟩))
    coreFresh absentFresh

/-- Node `[177]` yes → `[65]`, `lem:absorbed-germ-fan-data` (ii): at `G`'s
canonical absorbed half-edge, the decorated handoff fan data at the first high
centre `z` of its retained corridor -- the two corridor segments at `z` as the
arms of an envelope over the counted remainder core `Y` -- enters the common
Type B entry with the support `(Y, {z} ∪ centres(Y))` pinned by its charge
(`K .typeBAbsorbedCharge`). -/
@[reducible] noncomputable def absorbedGermFanEnvelopeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.absorbedGermFanEnvelope
    { Requires := [K .absorbedGermFanData, K .exactCollisionFails,
        K .typeBAbsorbedCharge, K .absorbedHandoffCore]
      Produces := [K .typeBFanEntry]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBFanEntry)
        ⟨Contracts.TypeB.typeBFanEntry_of_absorbedCore
          (inputs.get (K .exactCollisionFails)).down
          (inputs.get (K .absorbedGermFanData)).down
          (inputs.get (K .typeBAbsorbedCharge)).down
          (inputs.get (K .absorbedHandoffCore)).down⟩
        .nil)

/-- **Node `[177]` no: the (F4) charge** (user-approved extension of the cold
(F4) exact-count repair).  At `G`'s canonical absorbed half-edge without a
counted core, the half-edge is one of node `[219]`'s corridor-loss units,
within `(δ+1)·B_cold·σ(G)`, and is not routed through the Type B handoff. -/
@[reducible] noncomputable def absorbedF4ChargeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.absorbedF4Charge
    { Requires := [K .selection, K .uncompressible, K .remainderNormalized,
        K .absorbedGermFanData, K .coldGermCandidates,
        K .absorbedHandoffCoreAbsent, K .cubicBaseline]
      Produces := [K .absorbedF4Charge]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .absorbedF4Charge)
        ⟨Contracts.TypeB.absorbedF4Charge
          (inputs.get (K .selection)).down.1
          (inputs.get (K .uncompressible)).down
          (inputs.get (K .remainderNormalized)).down
          (inputs.get (K .cubicBaseline)).down.1.2.2.1
          (inputs.get (K .absorbedGermFanData)).down
          (inputs.get (K .coldGermCandidates)).down
          (inputs.get (K .absorbedHandoffCoreAbsent)).down⟩
        .nil)

/-- **Node `[176]` on the arm with neither a positive germ (`[175]` no) nor an
absorbed half-edge (`[177]` absent)**: G's selected cold branch-excess family is
empty and G has no ambient-cubic cold window
(`Contracts.Spine.coldSelectedFamilyEmpty_of_absent`). -/
@[reducible] noncomputable def coldSelectedFamilyEmptyRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldSelectedFamilyEmpty
    { Requires := [K .cubicBaseline, K .hotColdPartition, K .coldFailureRouting,
        K .coldNoPositiveGerm, K .typeBAbsorbedHalfEdgeAbsent]
      Produces := [K .coldSelectedFamilyEmpty]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldSelectedFamilyEmpty)
        ⟨Contracts.Spine.coldSelectedFamilyEmpty_of_absent data.toParameters
          inputs.current.object (inputs.get (K .cubicBaseline)).down.1.1
          (five_le_windowOrder_of_labelCount data.toParameters
            (inputs.get (K .cubicBaseline)).down.1.2.2.2.2.1)
          (inputs.get (K .hotColdPartition)).down
          (inputs.get (K .coldFailureRouting)).down
          (inputs.get (K .coldNoPositiveGerm)).down
          (inputs.get (K .typeBAbsorbedHalfEdgeAbsent)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
