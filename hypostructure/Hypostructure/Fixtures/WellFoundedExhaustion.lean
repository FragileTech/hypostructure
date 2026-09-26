import Hypostructure.Core.Strategy.WellFoundedExhaustion

/-!
# Core fixture for well-founded finite exhaustion

This fixture is deliberately domain-free.  It exercises one feedback step,
the strict measure proof, and a terminal target without importing Graph or
PDE code.
-/

namespace Hypostructure.Fixtures.WellFoundedExhaustion

open Hypostructure

def problem : Core.Problem where
  Ambient := Bool
  Baseline := fun _ => True
  BranchState := fun _ => Unit

def target : Core.Target problem where
  Predicate := fun _ => True
  Statement := True
  statement_to_target := fun statement _ _ => statement
  target_to_statement := fun _ => trivial

abbrev Input := Core.Strategy.ProblemInput problem

noncomputable def measure (input : Input) : Nat := by
  classical
  exact if input.object = true then 1 else 0

noncomputable def strategy : Core.Strategy.WellFoundedExhaustion problem target where
  Step := fun input => Subtype (fun _ : Unit => input.object = true)
  Handoff := fun _ => PEmpty
  Residual := fun _ => PEmpty
  measure := measure
  search := by
    classical
    exact fun input =>
      if h : input.object = true then
        .inl ⟨(), h⟩
      else
        .inr (.inl ⟨trivial⟩)
  replace := fun _ _ =>
    { object := false, baseline := trivial, branchState := () }
  measureDecreases := by
    classical
    intro input step
    simp only [measure]
    simp [step.property]
  transportTarget := fun _ _ _ => trivial
  transportHandoff := fun input step handoff => PEmpty.elim handoff
  transportResidual := fun input step residual => PEmpty.elim residual
  metadata := { name := "domain-neutral feedback fixture" }

noncomputable def dichotomy : Core.DichotomyData problem target :=
  strategy.toDichotomy

#print axioms dichotomy

end Hypostructure.Fixtures.WellFoundedExhaustion
