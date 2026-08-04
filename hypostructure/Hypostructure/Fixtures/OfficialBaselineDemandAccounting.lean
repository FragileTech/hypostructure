import Hypostructure.Core.Strategy.BaselineDemandAccounting
import Hypostructure.Fixtures.Budgets

namespace Hypostructure.Fixtures.OfficialBaselineDemandAccounting

open Hypostructure
open Hypostructure.Core.Strategy
open Hypostructure.Core.Residual

abbrev Previous := Ledger Unit

abbrev accountingSpec : CT5.Spec Previous where
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
  BaselineDemandAccounting.execution accounting

example (previous : Previous) :
    strategy.run previous = (CTAdapters.ct5 accounting).run previous :=
  rfl

example (previous : Previous) :
    strategy.checks previous = (CTAdapters.ct5 accounting).checks previous :=
  rfl

example (previous : Previous) :
    strategy.work previous = (CTAdapters.ct5 accounting).work previous :=
  rfl

end Hypostructure.Fixtures.OfficialBaselineDemandAccounting
