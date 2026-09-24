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

/-! ## Node `[117]`: the two-carrier decision on the object-level census

`prop:typeA-route8-carrier-reduction`, at the indexed route-8 entries of the
extracted Type A collection `𝒳_A` (`Graph.Route8Census.entries`: the
`(piece, receiver, silent-excess load)` triples with their selected trace basins
and canonical essential cores).  The manuscript's "some entry has `π_𝒳(ξ) ≤ 2`?"
is decided exhaustively; the yes arm carries the two-carrier entry to nodes
`[118]`--`[124]`, the no arm carries "every indexed entry has at least three
private essential boundary incidences" to the private-carrier census `[119]`--`[122]`, which
`K .route8Census` (deficit and rate) refutes. -/
/-! ## Node `[123]`: the unified negative Type A collection

`def:typeA-unified-negative` is a deterministic definition on the literal
incoming remainder.  It selects exactly the canonical supports with
`σ(X) = 0`, `N₀(X) < 0`, and no decorated Type B handoff, records the positive
cleared summand `s·δ(X) = |V(X)| - s·def⁺(X)` for each member, and names their
sum `s·\tilde D_A`.  It does not publish the next lower-bound lemma, any entry
classification, a carrier bound, or a peeling-stage invariant. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8UnifiedNegativeRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.route8UnifiedNegative
    { Requires := []
      Produces := [K .route8UnifiedNegative]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8UnifiedNegative)
        ⟨by
          classical
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          let packing := canonicalWindowPacking data inputs.current.object
          let support := inputs.current.object.remainderSupport packing
          let unified := (inputs.current.object.canonicalPieces support).filter
            fun component =>
              let piece := inputs.current.object.pieceSupport support component
              inputs.current.object.ambientSurplus piece data.threshold = 0 ∧
                inputs.current.object.NegativeNetCharge piece data.threshold
                  data.dischargeScale ∧
                ¬ HandoffProduced data inputs.current.object packing piece
          let collection := unified.image
            (inputs.current.object.pieceSupport support)
          refine ⟨collection, rfl, ?_,
            ∑ piece ∈ collection,
              (piece.card - data.dischargeScale *
                inputs.current.object.positiveDeficiency piece data.threshold), rfl⟩
          intro piece pieceMem
          rw [Finset.mem_image] at pieceMem
          obtain ⟨component, componentMem, rfl⟩ := pieceMem
          have selected := (Finset.mem_filter.mp componentMem).2
          obtain ⟨zero, negative, noHandoff⟩ := selected
          refine ⟨zero, negative, noHandoff, ?_⟩
          have deficitPositive :
              data.dischargeScale * inputs.current.object.positiveDeficiency
                  (inputs.current.object.pieceSupport support component)
                  data.threshold <
                (inputs.current.object.pieceSupport support component).card := by
            simpa [Graph.FiniteObject.NegativeNetCharge, zero] using negative
          exact Nat.sub_pos_iff_lt.mpr deficitPositive⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
