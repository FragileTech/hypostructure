import Hypostructure.Graph.Strategy.SpineRows.Node20aStructure
import HypostructureErdos64EG.Assembly.Final

open Hypostructure Hypostructure.Core.Residual Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine
universe u v

noncomputable section ExactHistory
variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation} {data : Data.{u}}
variable {current : Input BranchState Presentation presentation data}
variable {known : FactKeys (Input BranchState Presentation presentation data)}

/-- The row's output key list is literally singleton. -/
example :
    (originalCyclePassageRow (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)).manifest.Produces = [K .originalCyclePassage] := rfl

/-- The canonical runner retains the current object and every inherited key.
This checks an arbitrary literal incoming ledger, not a reconstructed cursor. -/
example (previous : ExactLedger (Input BranchState Presentation presentation data) current known)
    [Core.Strategy.FactKeys.Available
      (originalCyclePassageRow (BranchState := BranchState) (Presentation := Presentation)
        (presentation := presentation) (data := data)).manifest.Requires known]
    (fresh : List.Disjoint [K .originalCyclePassage] known) :
    ExactLedger (Input BranchState Presentation presentation data) current
      ([K .originalCyclePassage] ++ known) :=
  (originalCyclePassageRow (BranchState := BranchState) (Presentation := Presentation)
    (presentation := presentation) (data := data)).run previous fresh
end ExactHistory

#print axioms Hypostructure.Graph.CyclePassage.privateWedge_of_lift
#print axioms Hypostructure.Graph.CyclePassage.tightWedge_of_private
#print axioms Hypostructure.Graph.CyclePassage.contacts_in_positive_graph
#print axioms Hypostructure.Graph.Strategy.Spine.originalCyclePassageRow
#print axioms Hypostructure.Graph.Strategy.Spine.OriginalCyclePassageStatement.S1
#print axioms Hypostructure.Graph.Strategy.Spine.OriginalCyclePassageStatement.S2
#print axioms Hypostructure.Graph.Strategy.Spine.OriginalCyclePassageStatement.S3
#print axioms Hypostructure.Graph.Strategy.Spine.OriginalCyclePassageStatement.weakest_case
