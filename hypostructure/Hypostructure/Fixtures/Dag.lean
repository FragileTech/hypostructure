import Hypostructure.Core.Strategy.Dag
import Hypostructure.Fixtures.ClosingProgram

namespace Hypostructure.Fixtures.Dag

open Hypostructure.Core.Strategy
open Hypostructure.Core.Strategy.Dag
open Hypostructure.Fixtures.ClosingProgram
open scoped Hypostructure.Core.Strategy.Dag

noncomputable example :
    FactKeys.Available [prepared] [prepared, selection] := inferInstance

noncomputable def blueprint : Blueprint target :=
  Blueprint.root
    |>.scope scope
    |>.step prepare (name := "Prepare")
    |>.branch split
      (leftName := "True")
      (rightName := "False")

/-- Both decision leaves close automatically against the retained selection
fact.  The application supplies no keys, ledger, freshness proof, or closure
callback. -/
noncomputable def dag : ClosingDag target :=
  Hypostructure.Fixtures.ClosingProgram.dag

theorem certified_statement : target.Statement := dag.statement

noncomputable def partialDag : ClosingDag target :=
  dag

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.Blueprint.mk` -/
#guard_msgs (error) in
#check Blueprint.mk

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.Blueprint.body` -/
#guard_msgs (error) in
#check Blueprint.body

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.CompiledDag.dag` -/
#guard_msgs (error) in
#check CompiledDag.dag

#print axioms certified_statement

end Hypostructure.Fixtures.Dag
