import Hypostructure.Core.Strategy.ObstructionPackingSemantics
import Hypostructure.PDE.InducedPathColdQuery

/-!
# PDE adapter for obstruction packing

The represented PDE layer contributes only its exact cold-window schedule and
overlap semantics.  Core owns CT1, canonical maximal selection, branch routing,
and every ledger extension.
-/

namespace Hypostructure.PDE.Strategy.ObstructionPackingClosure

open Hypostructure

universe uInput uWindow uSite

/-- View the cold windows of a represented PDE residual as the occurrence
family consumed by the generic Core strategy.  Supports are residual-owned;
the adapter derives conflict as support overlap and supplies no selected
family or execution result. -/
noncomputable def coldWindowSemantics
    {Input : Type uInput} (Target : Input → Prop)
    (profile : InducedPathCold.Profile.{uInput, uWindow} Input)
    (Site : Input → Type uSite)
    (support : (input : Input) → profile.Window input → Finset (Site input))
    (noColdForcesTarget : ∀ input,
      InducedPathCold.coldValues profile input = [] → Target input) :
    Core.Strategy.ObstructionPackingClosure.Semantics
      Input Target where
  Occurrence := profile.Window
  occurrences := fun input =>
    (InducedPathCold.QuerySurface.coldWindowScheduleQuery profile).read input
  conflict := fun input left right =>
    ¬ Disjoint (support input left) (support input right)
  conflictDecidable := fun _ => Classical.decRel _
  conflictSymmetric := by
    intro input left right overlaps disjoint
    exact overlaps disjoint.symm
  freeForcesTarget := by
    intro input empty
    exact noColdForcesTarget input empty

end Hypostructure.PDE.Strategy.ObstructionPackingClosure
