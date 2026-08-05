import Hypostructure.Core.Strategy.ColdBranchAggregation

namespace Hypostructure.Fixtures.ColdBranchAggregation

open Hypostructure.Core.Strategy.ColdBranchAggregation

#check Registration
#check Profile.execution
#check Profile.residualQuery

example : Fintype.card Profile.Phase = 20 := by native_decide

noncomputable def samplePrefix : Prefix160 () where
  Interface := fun _ => Unit
  interface := ()
  contract146 := ⟨fun _ => ⟨0, 0⟩⟩
  Route := fun _ => Unit
  route := ()
  Private := fun _ => Unit
  privateData := ()
  Audit := fun _ => Unit
  audit := ()
  Cold := fun _ => Unit
  cold := ()
  Filter := fun _ => Unit
  filter := ()
  Stubs := fun _ => Unit
  stubs := ()
  Scan := fun _ => Unit
  scan := ()
  contract154 := ⟨fun _ => ⟨0, 0⟩⟩
  Certificate := fun _ => Unit
  certificate := ()
  contract156 :=
    { event := fun _ => True
      event_decidable := fun _ => inferInstance }
  Germ := fun _ => Unit
  germ := ()
  contract158 :=
    { scale := fun _ => 0
      bounded := fun _ => True
      bounded_of_scale := fun _ => trivial }
  contract159 :=
    { candidate := fun _ => Unit
      admissible := fun _ _ => True
      witness := fun _ => ⟨()⟩
      witness_admissible := fun _ => ⟨(), trivial⟩ }
  contract160 :=
    { good := fun _ => True
      good_decidable := fun _ => inferInstance }

noncomputable def inputs : Inputs () where
  toPrefix160 := samplePrefix
  Evidence := fun _ => Unit
  evidence := ()
  Residual := fun _ => Unit
  residual := ()
  contract163 :=
    { package := fun _ => Unit
      package_of_good := fun _ => ⟨()⟩ }
  Package := fun _ => Unit
  package := ()

noncomputable def profile : Profile Unit where
  registration.inputs := fun previous => by
    cases previous
    exact inputs

noncomputable def result := profile.execution.run ()

example : profile.execution.checks () = 20 := by rfl
example : profile.execution.work () = 20 := by rfl

/-! Every introduced fact is read from the final node-164 residual through
the public ledger-query surface. -/
example : inputs.interfaceAt164Query result = () := by rfl
example :
    match inputs.decision146At164Query result with
    | .yesBranch _ => False
    | .noBranch _ => True := by
  trivial
example : inputs.routeAt164Query result = () := by rfl
example : inputs.privateAt164Query result = () := by rfl
example : inputs.auditAt164Query result = () := by rfl
example : inputs.coldAt164Query result = () := by rfl
example : inputs.filterAt164Query result = () := by rfl
example : inputs.stubsAt164Query result = () := by rfl
example : inputs.scanAt164Query result = () := by rfl
example :
    match inputs.decision154At164Query result with
    | .yesBranch _ => False
    | .noBranch _ => True := by
  trivial
example : inputs.certificateAt164Query result = () := by rfl
example :
    match inputs.decision156At164Query result with
    | .yesBranch _ => True
    | .noBranch _ => False := by
  trivial
example : inputs.germAt164Query result = () := by rfl
example : True := by
  have _bounded := inputs.bounded158At164Query result
  trivial
example : True := by
  have _witness := inputs.witness159At164Query result
  trivial
example :
    match inputs.decision160At164Query result with
    | .yesBranch _ => True
    | .noBranch _ => False := by
  trivial
example : inputs.evidenceAt164Query result = () := by rfl
example : inputs.residual162At164Query result = () := by rfl
example : inputs.package163At164Query result = () := by rfl
example : inputs.package164At164Query result = () := by rfl

end Hypostructure.Fixtures.ColdBranchAggregation
