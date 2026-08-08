import Hypostructure.Graph.AtomResponse

namespace Hypostructure.Fixtures.GraphAtomResponse

open Hypostructure.Graph
open Hypostructure.Graph.AtomResponse

universe u v

variable {object : FiniteObject.{u}}
variable {atom : ProperBoundariedAtom object}
variable {Target : FiniteObject.{u} → Prop}
variable {Coordinate : Type v}

/-- Literal gluing of one fixed atom piece cannot witness a response defect
between two coordinate labels. -/
example (left right : Coordinate) :
    ¬ ∃ outside : OutsideContext atom.decomposition.interface,
      ¬ (CoordinateSystem.literalGluingTargetResponse
            atom.decomposition.piece Target left outside ↔
          CoordinateSystem.literalGluingTargetResponse
            atom.decomposition.piece Target right outside) :=
  CoordinateSystem.not_exists_literalGluingTargetDefect
    atom.decomposition.piece left right

end Hypostructure.Fixtures.GraphAtomResponse
