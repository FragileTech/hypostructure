import Hypostructure.Core.Residual.Decision

/-!
# Exhaustive destructor for a binary decision stage

A binary decision stage carries a literal predecessor and exactly one branch
proof.  Core owns the statement that those two constructors are the only
alternatives, so an application never restates the split, never rebuilds the
predecessor, and never re-derives the branch proof it already holds.

This is the framework-owned form of the "only two cases" checkpoint: the
literal predecessor and its branch proof are already carried by the ledger
extension, so the destructor introduces no routing and no problem data.
-/

namespace Hypostructure.Core.Residual.Decision

universe uPrevious

/-- **The two branches are the only alternatives.**

Every binary decision stage is literally the ledger extension of its own
retained predecessor by one of the two branch constructors.  Both disjuncts
expose the predecessor and the branch proof that the stage already carries;
nothing is recomputed. -/
theorem stage_extend_yes_or_extend_no
    {Previous : Sort uPrevious} {Yes No : Previous -> Prop}
    (stage : Stage Yes No) :
    (∃ previous : Previous, ∃ yes : Yes previous,
        stage = Ledger.extend previous (Binary.yesBranch yes)) ∨
    (∃ previous : Previous, ∃ no : No previous,
        stage = Ledger.extend previous (Binary.noBranch no)) := by
  cases added : stage.added with
  | yesBranch yes =>
      refine Or.inl ⟨stage.previous, yes, ?_⟩
      calc
        stage = Ledger.extend stage.previous stage.added :=
          (Ledger.extend_eta stage).symm
        _ = Ledger.extend stage.previous (Binary.yesBranch yes) := by
          rw [added]
  | noBranch no =>
      refine Or.inr ⟨stage.previous, no, ?_⟩
      calc
        stage = Ledger.extend stage.previous stage.added :=
          (Ledger.extend_eta stage).symm
        _ = Ledger.extend stage.previous (Binary.noBranch no) := by
          rw [added]

/-- The propositional shadow of `stage_extend_yes_or_extend_no`: the retained
predecessor of a binary decision stage satisfies one of the two outcomes. -/
theorem yes_or_no_of_stage
    {Previous : Sort uPrevious} {Yes No : Previous -> Prop}
    (stage : Stage Yes No) :
    Yes stage.previous ∨ No stage.previous := by
  cases stage.added with
  | yesBranch yes => exact Or.inl yes
  | noBranch no => exact Or.inr no

end Hypostructure.Core.Residual.Decision
