import Hypostructure.Core.Finite.Enumeration

/-!
# Residual-indexed obstruction-packing semantics

This lower-layer record is inert mathematical presentation data.  It has no
CT executor, ledger constructor, route, strategy result, or target-closing
callback.  The executable CT1 strategy lives in
`ObstructionPackingClosure.lean` and is the only layer permitted to consume
this record operationally.
-/

namespace Hypostructure.Core.Strategy.ObstructionPackingClosure

universe uInput uOccurrence

/-- The residual-owned occurrence family and its semantic obstruction-free
conclusion.  Core derives every packing and branch from this data. -/
structure Semantics (Input : Type uInput) (Target : Input → Prop) where
  Occurrence : Input → Type uOccurrence
  occurrences : (input : Input) →
    Core.Finite.Enumeration (Occurrence input)
  conflict : (input : Input) →
    Occurrence input → Occurrence input → Prop
  conflictDecidable : (input : Input) →
    DecidableRel (conflict input)
  conflictSymmetric : ∀ input, Symmetric (conflict input)
  freeForcesTarget : ∀ input,
    (occurrences input).values = [] → Target input

end Hypostructure.Core.Strategy.ObstructionPackingClosure
