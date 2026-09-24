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

/-! ## Node `[35]`: separated testers

`lem:separated-testers`.  Let corresponding internal wedges be centred in
vertex-disjoint isomorphic rooted radius-`r` balls.  If an exact owned
decomposition has those two balls as its piece side, every internal vertex of
its outside context lies in the complement of both balls.  Thus any outside
context distinguishing the represented wedges is supported there.  For an
attempted quotient identifying their labels, excluded middle on context
equivalence gives precisely the paper's concluding alternative: every
identified pair is context-universal, or an identified pair has a concrete
target-defect context.

This is a source-free Type-A row: all objects occur in the proposition and the
proof reads only `inputs.current`.  The row introduces no proof-specific data
carrier and appends its sole output to the literal `ExactLedger`. -/
@[reducible] noncomputable def separatedTestersRow
    (data : Data.{u}) :
    AtomicStrategy (Input BranchState Presentation presentation data) := by
  classical
  exact
    factOnly `Hypostructure.Graph.Strategy.Spine.separatedTesters
      (sourceFreeManifest (K .separatedTesters))
      (fun inputs =>
        .cons (key := K .separatedTesters)
          ⟨by
            intro packing _valid _packingCard radius u v _uMem _vMem
            dsimp only
            intro leftWedge rightWedge _leftMem _rightMem _leftRoot _rightRoot
              _sameType _disjoint
            constructor
            · intro decomposition pieceCovers represented _separates internal
              constructor <;> intro inBall
              · obtain ⟨inside, same⟩ :=
                  (pieceCovers _).mp (Or.inl inBall)
                have impossible :
                    Graph.pieceEmbedding decomposition.piece
                        decomposition.outside inside =
                      Graph.contextEmbedding decomposition.piece
                        decomposition.outside (.inr internal) := by
                  apply decomposition.vertexEquiv.injective
                  simpa [Graph.OwnedDecomposition.pieceIntoAmbient] using same
                cases inside <;>
                  simp [Graph.pieceEmbedding, Graph.contextEmbedding] at impossible
              · obtain ⟨inside, same⟩ :=
                  (pieceCovers _).mp (Or.inr inBall)
                have impossible :
                    Graph.pieceEmbedding decomposition.piece
                        decomposition.outside inside =
                      Graph.contextEmbedding decomposition.piece
                        decomposition.outside (.inr internal) := by
                  apply decomposition.vertexEquiv.injective
                  simpa [Graph.OwnedDecomposition.pieceIntoAmbient] using same
                cases inside <;>
                  simp [Graph.pieceEmbedding, Graph.contextEmbedding] at impossible
            · intro attempt _identified
              by_cases universal :
                  ∀ left right : Graph.BoundaryPiece
                      (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary
                        inputs.current.object attempt.support),
                    attempt.Identifies left right →
                      Graph.Response.ContextEquivalent
                        (Graph.HasCycleWithLength data.LengthOK) left right
              · exact Or.inl universal
              · right
                push Not at universal
                obtain ⟨left, right, sameValues, failure⟩ := universal
                exact ⟨left, right, sameValues,
                  Graph.Response.targetDefect_of_not_contextEquivalent failure⟩⟩
          .nil)

end Hypostructure.Graph.Strategy.Spine
