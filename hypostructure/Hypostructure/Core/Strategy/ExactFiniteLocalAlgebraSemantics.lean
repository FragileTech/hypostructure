import Hypostructure.Core.Finite.Enumeration

/-!
# Residual-indexed exact finite algebra semantics

These are inert finite presentation records.  They contain schedules and
denotations only; CT9/CT16 execution and ledger composition remain in
`ExactFiniteLocalAlgebra.lean`.
-/

namespace Hypostructure.Core.Strategy.ExactFiniteLocalAlgebra

universe uInput uItem uLabel uRelation

/-- Residual-indexed finite label and relation semantics. -/
structure Semantics (Input : Type uInput) where
  Label : Input → Type uLabel
  labels : (input : Input) →
    Core.Finite.CompleteEnumeration (Label input)
  capacity : (input : Input) → Label input → Nat
  RelationIndex : Input → Type uRelation
  relationIndices : (input : Input) →
    Core.Finite.CompleteEnumeration (RelationIndex input)
  relation : (input : Input) →
    RelationIndex input → Label input → Label input → Bool
  /-- Optional generated-table representation of the relation code.  This is
  data only: the following field forces it to be exactly the code determined
  by the complete semantic schedules above. -/
  targetCode : (input : Input) → List Bool
  targetCode_exact : ∀ input,
    targetCode input =
      ((relationIndices input).toEnumeration.product
        ((labels input).toEnumeration.product
          (labels input).toEnumeration)).values.map fun coordinate =>
            relation input coordinate.1 coordinate.2.1 coordinate.2.2

/-- One residual-owned item family to which the exact finite semantics is
applied.  This record cannot execute either CT or construct an output. -/
structure Registration (Input : Type uInput) where
  Item : Input → Type uItem
  items : (input : Input) → Core.Finite.Enumeration (Item input)
  semantics : Semantics.{uInput, uLabel, uRelation} Input
  label : (input : Input) → Item input → semantics.Label input

end Hypostructure.Core.Strategy.ExactFiniteLocalAlgebra
