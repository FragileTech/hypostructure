import Hypostructure.Core.Strategy.OfficialRegistry

/-!
# Official reusable program syntax

`Program` is the sole author-facing control-flow language.  It contains only
closed official strategy references, labels, and lossless composition.  It
cannot contain an executor, classifier, transition, closure, or proof.
-/

namespace Hypostructure.Core.Strategy.Official

open OfficialRegistry

structure Label where
  text : String
  deriving Repr, Inhabited, DecidableEq

/-- Reusable, callback-free strategy composition. -/
inductive Program where
  | done
  | invoke (label : Label) (strategy : Ref)
  | chain (label : Label) (head tail : Program)
  | branch (label : Label) (strategy : Ref) (continuations : List Program)
  | join (label : Label) (branches : List Program) (continuation : Program)
  deriving Repr, Inhabited

namespace Program

def references : Program → List Ref
  | .done => []
  | .invoke _ ref => [ref]
  | .chain _ head tail => head.references ++ tail.references
  | .branch _ ref continuations => ref :: continuations.flatMap references
  | .join _ branches continuation =>
      branches.flatMap references ++ continuation.references

def labels : Program → List String
  | .done => []
  | .invoke label _ => [label.text]
  | .chain label head tail => label.text :: (head.labels ++ tail.labels)
  | .branch label _ continuations =>
      label.text :: continuations.flatMap labels
  | .join label branches continuation =>
      label.text :: (branches.flatMap labels ++ continuation.labels)

def size : Program → Nat
  | .done => 0
  | .invoke _ _ => 1
  | .chain _ head tail => head.size + tail.size
  | .branch _ _ continuations => 1 + (continuations.map size).sum
  | .join _ branches continuation =>
      (branches.map size).sum + continuation.size

/-- Strategy invocations whose exhaustive residual-continuation arity is
explicit in the program.  Framework-owned target closure is not represented
by a continuation and therefore never contributes to this count.  A bare
`invoke` is a reusable linear atom; its residual continuation is supplied by
surrounding composition. -/
def arities : Program → List (Ref × Nat)
  | .done | .invoke .. => []
  | .chain _ head tail => head.arities ++ tail.arities
  | .branch _ ref continuations =>
      (ref, continuations.length) :: continuations.flatMap arities
  | .join _ branches continuation =>
      branches.flatMap arities ++ continuation.arities

end Program

end Hypostructure.Core.Strategy.Official
