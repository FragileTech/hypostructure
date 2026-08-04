import Hypostructure.Core.Strategy
import Hypostructure.Core.Residual.DecisionExhaustion

/-!
# The canonical closed dichotomy of a binary decision stage

Core already decides a registered binary node and retains the selected branch
proof in the ledger.  This module turns that retained decision into Core's
own `ClosedDichotomy`, so a strategy that has to route on an earlier binary
decision reads the classification off the ledger instead of registering a
second classifier.

Both branch payloads are the proof data the predecessor stage already carries;
Core owns the classification and the closed branch algebra.
-/

namespace Hypostructure.Core.Strategy

universe uPrevious

open Hypostructure.Core.Residual

/-- The closed dichotomy carried by a binary decision stage.  The left branch
is the negative outcome and the right branch the positive one, matching the
`Sum`-orientation Core uses everywhere for routed continuations. -/
def binaryClosedDichotomy {Previous : Type uPrevious}
    (Yes No : Previous -> Prop) :
    ClosedDichotomy (Residual.Decision.Stage Yes No) where
  LeftPayload stage := ProofPayload (No stage.previous)
  RightPayload stage := ProofPayload (Yes stage.previous)
  classify stage :=
    match stage.added with
    | .yesBranch yes => Sum.inr ⟨yes⟩
    | .noBranch no => Sum.inl ⟨no⟩
  leftClosed stage _payload := No stage.previous
  rightClosed stage _payload := Yes stage.previous
  leftProof stage := by
    cases added : stage.added with
    | yesBranch yes => simp
    | noBranch no => simpa [added] using no
  rightProof stage := by
    cases added : stage.added with
    | yesBranch yes => simpa [added] using yes
    | noBranch no => simp

/-- The classification really is the retained decision: a stage whose added
branch is positive is routed right. -/
@[simp] theorem binaryClosedDichotomy_classify_yesBranch
    {Previous : Type uPrevious} {Yes No : Previous -> Prop}
    (previous : Previous) (yes : Yes previous) :
    (binaryClosedDichotomy Yes No).classify
        (Ledger.extend previous (Residual.Decision.Binary.yesBranch yes)) =
      Sum.inr ⟨yes⟩ :=
  rfl

/-- The classification really is the retained decision: a stage whose added
branch is negative is routed left. -/
@[simp] theorem binaryClosedDichotomy_classify_noBranch
    {Previous : Type uPrevious} {Yes No : Previous -> Prop}
    (previous : Previous) (no : No previous) :
    (binaryClosedDichotomy Yes No).classify
        (Ledger.extend previous (Residual.Decision.Binary.noBranch no)) =
      Sum.inl ⟨no⟩ :=
  rfl

/-- **The closed branch algebra of a retained binary decision.**

Whichever way the retained decision classified, the corresponding branch
proposition holds of the literal predecessor.  This is
`ClosedDichotomy.closed` read at the binary decision stage: the destructor
`Residual.Decision.stage_extend_yes_or_extend_no` and this dichotomy decide
the identical proposition. -/
theorem binaryClosedDichotomy_closed {Previous : Type uPrevious}
    (Yes No : Previous -> Prop) (stage : Residual.Decision.Stage Yes No) :
    No stage.previous ∨ Yes stage.previous := by
  have closed := (binaryClosedDichotomy Yes No).closed stage
  cases added : stage.added with
  | yesBranch yes =>
      rw [show (binaryClosedDichotomy Yes No).classify stage = Sum.inr ⟨yes⟩ from
        by simp [binaryClosedDichotomy, added]] at closed
      exact Or.inr closed
  | noBranch no =>
      rw [show (binaryClosedDichotomy Yes No).classify stage = Sum.inl ⟨no⟩ from
        by simp [binaryClosedDichotomy, added]] at closed
      exact Or.inl closed

end Hypostructure.Core.Strategy
