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

/-! ## Two-terminal closure (no manuscript label; not a manuscript statement) -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def gadgetClosureRow :
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
    `Hypostructure.Graph.Strategy.Spine.gadgetClosure
    { Requires := [K .selection, K .cubicBaseline]
      Produces := [K .gadgetClosure]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selection := (inputs.get (K .selection)).down
      let cubic := (inputs.get (K .cubicBaseline)).down.1
      .cons (key := K .gadgetClosure) ⟨by
        classical
        dsimp only [Holds]
        let avoids (piece : Graph.FiniteObject.{u}) :=
          ¬ Graph.HasCycleWithLength data.LengthOK piece
        let cubicPiece (piece : Graph.FiniteObject.{u}) (x y : piece.Vertex) :=
          x ≠ y ∧ piece.degree x = 2 ∧ piece.degree y = 2 ∧
            ∀ vertex, vertex ≠ x → vertex ≠ y → piece.degree vertex = 3
        have minimal : ∀ candidate : Graph.FiniteObject.{u},
            candidate.LexicographicallySmaller inputs.current.object →
            3 ≤ candidate.minDegree →
            Graph.HasCycleWithLength data.LengthOK candidate := by
          intro candidate smaller baseline
          apply selection.2.sizeMinimal candidate smaller
          rw [cubic]
          exact baseline
        have accepted (length : Nat) : data.LengthOK length ↔
            Core.DyadicLength.PowerOfTwoLength length :=
          data.lengthOK_iff_powerOfTwo length
        constructor
        · intro left right a b c d leftCubic rightCubic leftAvoids rightAvoids
            count baseline
          have smaller :
              (Graph.TwoTerminalClosure.close left right a b c d).LexicographicallySmaller
                inputs.current.object :=
            Graph.FiniteObject.lexicographicallySmaller_of_vertexCount_lt (by
              rw [Graph.TwoTerminalClosure.vertexCount_close]
              exact count)
          obtain ⟨leftPath, rightPath, leftIsPath, rightIsPath, lengthOK⟩ :=
            Graph.TwoTerminalClosure.terminal_paths_of_minimal_closure
              inputs.current.object left right a b c d leftCubic.1 rightCubic.1
              leftAvoids rightAvoids smaller baseline minimal
          exact ⟨leftPath, rightPath, leftIsPath, rightIsPath,
            (accepted _).mp lengthOK⟩
        · constructor
          · intro piece a b count pieceCubic pieceAvoids baseline
            have smaller : (piece.addEdge a b).LexicographicallySmaller
                inputs.current.object :=
              Graph.FiniteObject.lexicographicallySmaller_of_vertexCount_lt (by
                simpa using count)
            obtain ⟨path, pathIsPath, lengthOK⟩ :=
              Graph.AddedEdgeClosure.terminalPath_of_minimal_addedEdge
                inputs.current.object piece a b pieceCubic.1 pieceAvoids smaller
                baseline minimal
            obtain ⟨exponent, exponentLower, equality⟩ :=
              (Core.DyadicLength.powerOfTwoLength_iff _).mp
                ((accepted _).mp lengthOK)
            exact ⟨path, exponent, pathIsPath, by omega, by omega⟩
          · constructor
            · intro piece a b count pieceCubic pieceAvoids baseline
              have smaller :
                  (Graph.TwoTerminalClosure.close piece piece a b a b).LexicographicallySmaller
                    inputs.current.object :=
                Graph.FiniteObject.lexicographicallySmaller_of_vertexCount_lt (by
                  rw [Graph.TwoTerminalClosure.vertexCount_close]
                  simpa [two_mul] using count)
              obtain ⟨first, second, firstPath, secondPath, lengthOK⟩ :=
                Graph.TwoTerminalClosure.terminal_paths_of_minimal_closure
                  inputs.current.object piece piece a b a b pieceCubic.1 pieceCubic.1
                  pieceAvoids pieceAvoids smaller baseline minimal
              obtain ⟨exponent, _lower, equality⟩ :=
                (Core.DyadicLength.powerOfTwoLength_iff _).mp
                  ((accepted _).mp lengthOK)
              exact ⟨first, second, exponent, firstPath, secondPath, by omega⟩
            · intro support complementSupport
              dsimp
              intro t1 t2 u1 u2 _isComplement _pieceCubic _pieceAvoids complementAvoids
                different _nonadjacent _attachment smaller baseline
              obtain ⟨path, pathIsPath, lengthOK⟩ :=
                Graph.AddedEdgeClosure.terminalPath_of_minimal_addedEdge
                  inputs.current.object _ u1 u2 different complementAvoids smaller
                  baseline minimal
              obtain ⟨exponent, exponentLower, equality⟩ :=
                (Core.DyadicLength.powerOfTwoLength_iff _).mp
                  ((accepted _).mp lengthOK)
              exact ⟨path, exponent, pathIsPath, by omega, by omega⟩
      ⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
