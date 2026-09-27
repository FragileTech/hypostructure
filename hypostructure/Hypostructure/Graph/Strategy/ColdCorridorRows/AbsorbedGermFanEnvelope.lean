import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Entry

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
half-edge outside node `[153]`'s subcubic candidates has its own pinned absorbed
Type B support `(J_ε, {z_ε})` --- the prefix of its corridor through its first
high centre `z_ε` --- and that support's negative part is charged to the
surplus of `z_ε` (`lem:typeB-bridge-deficit-bound`). -/
@[reducible] noncomputable def typeBAbsorbedChargeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBAbsorbedCharge
    { Requires := [K .selection, K .uncompressible, K .remainderNormalized,
        K .absorbedGermFanData, K .cubicBaseline]
      Produces := [K .typeBAbsorbedCharge]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBAbsorbedCharge)
        ⟨Contracts.TypeB.typeBAbsorbedCharge
          (Contracts.TypeB.absorbedGermDecoratedAssignedSupport
            (inputs.get (K .selection)).down.1
            (inputs.get (K .uncompressible)).down
            (inputs.get (K .remainderNormalized)).down
            (inputs.get (K .absorbedGermFanData)).down
            (le_of_eq (inputs.get (K .cubicBaseline)).down.1.1.symm)
            (inputs.get (K .cubicBaseline)).down.1.2.2.1)
          (fun vertex => le_trans inputs.current.baseline
            (inputs.current.object.minDegree_le_degree vertex))
          (inputs.get (K .cubicBaseline)).down.2.1.2.2.2.2⟩
        .nil)

/-- Node `[177]` → `[65]`, `lem:absorbed-germ-fan-data` (ii): at `G`'s canonical
absorbed half-edge (the `[175]` yes arm), its pinned charge
(`K .typeBAbsorbedCharge`) enters the common Type B entry with the support
(prefix through the first high centre `z`, `{z}`). -/
@[reducible] noncomputable def absorbedGermFanEnvelopeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.absorbedGermFanEnvelope
    { Requires := [K .absorbedGermFanData, K .exactCollisionFails,
        K .typeBAbsorbedCharge, K .typeBAbsorbedHalfEdge]
      Produces := [K .typeBFanEntry]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBFanEntry)
        ⟨Contracts.TypeB.typeBFanEntry_of_absorbedHalfEdge
          (inputs.get (K .exactCollisionFails)).down
          (inputs.get (K .absorbedGermFanData)).down
          (inputs.get (K .typeBAbsorbedCharge)).down
          (inputs.get (K .typeBAbsorbedHalfEdge)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
