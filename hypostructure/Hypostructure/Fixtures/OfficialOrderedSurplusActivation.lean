import Hypostructure.Core.Strategy.OrderedSurplusActivation
import Hypostructure.Fixtures.Budgets

namespace Hypostructure.Fixtures.OfficialOrderedSurplusActivation

open Hypostructure
open Hypostructure.Core.Strategy
open Hypostructure.Core.Residual

abbrev Previous := Ledger Unit

abbrev activitySpec : CT6.Spec Previous where
  Index := fun _ => Unit
  FailureData := fun _ _ => Empty
  Failure := fun _ _ => False
  failureData := fun _ _ failure => failure.elim
  contribution := fun _ _ => Fintype.card Unit

def activity : CT6.Capability activitySpec where
  failureOrder :=
    Query.ofFunction fun _ => Core.Finite.Enumeration.singleton ()
  failureDecidable := fun _ _ => isFalse id
  inputSize := fun _ => Fintype.card Unit
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro previous
    simp [CT6.localCheckBound, Core.Finite.Enumeration.card,
      Core.Finite.Enumeration.singleton, Core.Finite.Enumeration.ofNodupList]

abbrev ActivityStage :=
  Ledger.Extension Previous (CTAdapters.ct6 activity).Output

abbrev accountingSpec : CT5.Spec ActivityStage where
  budget := Hypostructure.Fixtures.Budgets.naturalResource
  Site := fun _ => Unit
  Witness := fun _ _ => Unit
  Active := fun _ _ => True
  Supports := fun _ _ _ => True
  contribution := fun _ _ _ => Fintype.card Unit
  required := fun _ => Fintype.card Unit
  capacity := fun _ => Fintype.card Unit

def accounting : CT5.Capability accountingSpec where
  family := Query.ofFunction fun _ =>
    { indices := Core.Finite.Enumeration.singleton ()
      fibres := fun _ => Core.Finite.Enumeration.singleton () }
  activeDecidable := fun _ _ => isTrue trivial
  supportsDecidable := fun _ _ _ => isTrue trivial
  resourceLEDecidable := Nat.decLe

noncomputable def strategy : CTExecution Previous :=
  OrderedSurplusActivation.execution activity accounting

example (previous : Previous) :
    (strategy.run previous).fst = (CTAdapters.ct6 activity).run previous :=
  CTExecution.compose_run_first _ _ _

example (previous : Previous) :
    (strategy.run previous).snd =
      (CTAdapters.ct5 accounting).run
        (Ledger.extend previous ((CTAdapters.ct6 activity).run previous)) :=
  CTExecution.compose_run_next _ _ _

example (previous : Previous) :
    strategy.checks previous =
      (CTAdapters.ct6 activity).checks previous +
        (CTAdapters.ct5 accounting).checks
          (Ledger.extend previous ((CTAdapters.ct6 activity).run previous)) :=
  rfl

example (previous : Previous) :
    strategy.work previous =
      (CTAdapters.ct6 activity).work previous +
        (CTAdapters.ct5 accounting).work
          (Ledger.extend previous ((CTAdapters.ct6 activity).run previous)) :=
  rfl

end Hypostructure.Fixtures.OfficialOrderedSurplusActivation
