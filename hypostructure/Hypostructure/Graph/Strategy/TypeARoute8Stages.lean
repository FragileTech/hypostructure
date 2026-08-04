import Hypostructure.Graph.TypeARoute8Carriers
import Hypostructure.Graph.Strategy.TypeAReceiverStages


namespace Hypostructure.Graph.Strategy.TypeARoute8Stages

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy.FiniteStateNetChargeContinuation
open Hypostructure.Graph.Strategy.TypeAReceiverStages

universe uPrevious uResidual

variable {Previous : Type uPrevious} {Residual : Type uResidual}
variable [HasResidual Previous Residual]
variable (profile : Profile Previous Residual)


noncomputable def deficit111 {previous : Previous}
    (residual : profile.TypeAResidual previous) (discharge : Nat) : Nat :=
  (summaryAt profile residual).netDeficiency.remainder -
    discharge * (summaryAt profile residual).requiredMass

structure Collection111 {previous : Previous}
    (residual : profile.TypeAResidual previous) where
  /-- `N_basin(𝒳_A)`, the number of indexed trace-basin entries. -/
  entryCount : Nat

abbrev Stage111 {previous : Previous}
    (residual : profile.TypeAResidual previous) :=
  Ledger.Extension (Stage91 profile residual)
    (fun _ => Collection111 profile residual)

/-- Append the collection to the ledger. -/
noncomputable def stage111 {previous : Previous}
    (residual : profile.TypeAResidual previous)
    (stage : Stage91 profile residual)
    (collection : Collection111 profile residual) :
    Stage111 profile residual :=
  Ledger.extend stage collection

/-- Recover the node-`[111]` collection through the ledger API. -/
def collection111Query {previous : Previous}
    (residual : profile.TypeAResidual previous) :
    Query (Stage111 profile residual)
      (fun _ => Collection111 profile residual) :=
  Query.latest


abbrev Burden112 {previous : Previous}
    {residual : profile.TypeAResidual previous}
    (discharge : Nat) (collection : Collection111 profile residual) : Prop :=
  discharge * deficit111 profile residual discharge ≤ collection.entryCount

abbrev Deficit113 {previous : Previous}
    {residual : profile.TypeAResidual previous}
    (discharge : Nat) (collection : Collection111 profile residual) : Prop :=
  (summaryAt profile residual).netDeficiency.remainder ≤
    discharge * deficit111 profile residual discharge +
      discharge * (summaryAt profile residual).requiredMass


theorem contradiction122 {previous : Previous}
    {residual : profile.TypeAResidual previous}
    {discharge required : Nat}
    {collection : Collection111 profile residual}
    (dischargePos : 0 < discharge) (requiredPos : 0 < required)
    (burden : Burden112 profile discharge collection)
    (deficit : Deficit113 profile discharge collection)
    (budget : required * collection.entryCount ≤
      (summaryAt profile residual).requiredMass)
    (rate : (required * discharge + 1) *
        (summaryAt profile residual).requiredMass <
      required * (summaryAt profile residual).netDeficiency.remainder) :
    False :=
  Graph.TypeARoute8Carriers.carrierBudgetContradiction
    dischargePos requiredPos burden deficit budget rate

end Hypostructure.Graph.Strategy.TypeARoute8Stages
