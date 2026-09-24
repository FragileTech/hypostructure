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

/-! ## `thm:branch-kill`: the all-pieces classification at the canonical packing

The contrapositive of clauses (a) and (b) at every negative piece of the
canonical decomposition, assembled from the two committed ∀-piece facts: the
zero-surplus arm is `lem:typeA-exclusion`'s "Consequently" trichotomy read from
`K .typeAExclusion`, and the positive-surplus arm is
`prop:typeB-bridge-reduction`'s contrapositive read from
`K .typeBBridgeReduction` — the B2 disjoint ledger with strictly negative
remaining core, or a minimal overlap obstruction; the post-ledger hygiene and
grouped coverage remain on that key and are not republished.  Maximality of the
canonical packing is derived, not assumed
(`exists_mem_not_disjoint_of_card_eq`). -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8PiecesClassifiedRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
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
    `Hypostructure.Graph.Strategy.Spine.route8PiecesClassified
    { Requires := [K .typeAExclusion, K .typeBBridgeReduction]
      Produces := [K .route8PiecesClassified]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let exclusion := (inputs.get (K .typeAExclusion)).down
      let bridge := (inputs.get (K .typeBBridgeReduction)).down
      .cons (key := K .route8PiecesClassified)
        (⟨by
          classical
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          have packingSpec := Classical.choose_spec
            (inputs.current.object.exists_windowPacking_card_eq data.windowOrder)
          have valid : inputs.current.object.IsWindowPacking data.windowOrder
              (canonicalWindowPacking data inputs.current.object) :=
            packingSpec.1
          have maximal : ∀ window : Finset inputs.current.object.Vertex,
              inputs.current.object.InducesWindow data.windowOrder window →
              ∃ member ∈ canonicalWindowPacking data inputs.current.object,
                ¬ Disjoint window member := fun window induces =>
            inputs.current.object.exists_mem_not_disjoint_of_card_eq
              data.windowOrder_pos valid packingSpec.2 induces
          intro piece pieceMem negative
          refine ⟨?_, ?_⟩
          · -- `thm:branch-kill`(a): the `[86]` trichotomy at this exact piece,
            -- the support-general exclusion instantiated at the canonical one.
            intro zeroSurplus
            exact (exclusion (canonicalWindowPacking data inputs.current.object)
              valid maximal
              (inputs.current.object.pieceSupport
                (inputs.current.object.remainderSupport
                  (canonicalWindowPacking data inputs.current.object)) piece)
              (inputs.current.object.pieceSupport_subset _ piece)
              (Graph.SupportComponents.Connected.connectedOn_of_mem_order
                inputs.current.object _
                ((Graph.FiniteObject.mem_canonicalPieces _ _).1 pieceMem))
              negative zeroSurplus).1
          · -- `thm:branch-kill`(b): the bridge-residual dichotomy at this
            -- exact piece, with the hygiene clauses left on their own key.
            intro positiveSurplus
            rcases bridge (canonicalWindowPacking data inputs.current.object)
                valid maximal ⟨piece, pieceMem⟩ negative positiveSurplus with
              ⟨ledger, exactRefinement, notClean, _postLedger, _grouped⟩ |
                obstruction
            · exact Or.inl ⟨ledger, exactRefinement, notClean⟩
            · exact Or.inr obstruction⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
