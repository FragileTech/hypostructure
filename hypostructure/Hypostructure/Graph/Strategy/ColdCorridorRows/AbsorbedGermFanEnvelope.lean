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

/-- Node `[177]` → `[65]`, `lem:absorbed-germ-fan-data` (ii): at `G`'s canonical
absorbed half-edge (the `[175]` yes arm), the decorated handoff fan data at the
first high centre of its retained corridor enters the common Type B entry with
the support (first-failure prefix, `{centre}`). -/
@[reducible] noncomputable def absorbedGermFanEnvelopeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.absorbedGermFanEnvelope
    { Requires := [K .selection, K .uncompressible, K .remainderNormalized,
        K .absorbedGermFanData, K .exactCollisionFails, K .typeBAbsorbedHalfEdge,
        K .cubicBaseline]
      Produces := [K .typeBFanEntry]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBFanEntry)
        ⟨Contracts.TypeB.typeBFanEntry_of_absorbedHalfEdge
          (inputs.get (K .exactCollisionFails)).down
          (inputs.get (K .absorbedGermFanData)).down
          (Contracts.TypeB.absorbedGermDecoratedAssignedSupport
            (inputs.get (K .selection)).down.1
            (inputs.get (K .uncompressible)).down
            (inputs.get (K .remainderNormalized)).down
            (inputs.get (K .absorbedGermFanData)).down
            (le_of_eq (inputs.get (K .cubicBaseline)).down.1.symm)
            (inputs.get (K .cubicBaseline)).down.2.2.1)
          (inputs.get (K .typeBAbsorbedHalfEdge)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
