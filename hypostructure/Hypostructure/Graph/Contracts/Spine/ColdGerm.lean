import Hypostructure.Graph.Statements.Spine

/-!
# Contracts: bounded cold configurations `[154]`--`[157]`

Proof-agnostic contract lemmas for `lem:cold-bounded-germ-trichotomy`.  This
module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

/-- **G2 is a target-defective quotient, hence a sparse exit (b)**
(`lem:cold-bounded-germ-trichotomy`, case G2; `lem:context-universality`).
The two same-interface representatives `Q[x,y]` (the germ's own piece) and `E`
(its second representative) are identified by the germ's cold corridor state:
the attempted quotient on the germ's connected support has the two
representatives as its coordinates and one label for both, so it is
rank-reducing and identifies `Q` with `E`.  G2's distinguishing context is a
target defect of that identification.  Since the identification is not
target-complete, the admissibility clauses of the attempt are vacuous, and the
result is the sparse surplus exit (b) of `def:named-surplus-exits`. -/
theorem sparseSurplusExit_of_distinguishing
    {S : ColdCorridor.DeclaredSignature}
    {Baseline Target : FiniteObject.{u} → Prop} (LengthOK : Nat → Prop)
    {object : FiniteObject.{u}}
    (germ : ColdCorridor.BoundedGerm S Baseline Target object)
    (distinguishing : germ.Distinguishing) :
    SparseSurplusExit Baseline Target LengthOK object := by
  classical
  have notComplete : ¬ Response.ContextEquivalent Target germ.piece germ.canonical := by
    intro equivalent
    obtain ⟨outside, distinguishes⟩ := distinguishing
    exact distinguishes (equivalent outside)
  let attempt : AttemptedQuotient Baseline Target object
      (Finset.univ : Finset (ULift.{u} Bool)) (fun _ => germ.support) :=
    { support := germ.support
      connected := germ.connected
      carries := fun _ _ => Finset.Subset.refl _
      Label := PUnit
      Value := PUnit
      label := fun _ => PUnit.unit
      value := fun _ _ => PUnit.unit
      properRepresentative := fun _ _ complete =>
        absurd (complete germ.piece germ.canonical fun _ _ => rfl).2 notComplete
      closedRepresentative := fun covers _ complete =>
        absurd (complete germ.piece germ.canonical fun _ _ => rfl).2 notComplete }
  have reducing : ¬ Set.InjOn attempt.label
      ↑(Finset.univ : Finset (ULift.{u} Bool)) := by
    intro injective
    have same := injective (by simp) (by simp)
      (show attempt.label ⟨false⟩ = attempt.label ⟨true⟩ from rfl)
    exact Bool.false_ne_true (congrArg ULift.down same)
  exact .targetDefect Finset.univ (fun _ => germ.support) attempt reducing
    germ.piece germ.canonical (fun _ _ => rfl) distinguishing

end Hypostructure.Graph.Contracts.Spine
