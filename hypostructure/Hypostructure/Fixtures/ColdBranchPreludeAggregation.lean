import Hypostructure.Graph.Strategy.ColdBranchPreludeAggregation

namespace Hypostructure.Fixtures.ColdBranchPreludeAggregation

open Hypostructure
open Hypostructure.Graph.Strategy.ColdBranchPreludeAggregation

noncomputable def preludeInputsFor (surplus : Nat) : Inputs () where
  Net := fun _ => Unit
  net := ()
  Charge := fun _ => Unit
  charge := ()
  contract59 := ⟨fun _ => ⟨0, 0⟩⟩
  Closed := fun _ => Unit
  closed := ()
  Component := fun _ => Unit
  component := ()
  contract62 := ⟨fun _ => ⟨surplus, 0⟩⟩
  Handoff := fun _ => Unit
  handoff := ()
  Residual := fun _ => Unit
  residual := ()

noncomputable def preludeInputs : Inputs () :=
  preludeInputsFor 0

noncomputable def coldPrefix (previous : Previous) :
    Core.Strategy.ColdBranchAggregation.Prefix160 previous where
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

noncomputable def coldInputs (previous : Previous) :
    Core.Strategy.ColdBranchAggregation.Inputs previous where
  toPrefix160 := coldPrefix previous
  Evidence := fun _ => Unit
  evidence := ()
  Residual := fun _ => Unit
  residual := ()
  contract163 :=
    { package := fun _ => Unit
      package_of_good := fun _ => ⟨()⟩ }
  Package := fun _ => Unit
  package := ()

noncomputable def combinedInputs : CombinedInputs () where
  toInputs := preludeInputs
  cold := coldInputs preludeInputs.stage64

noncomputable def preludeInputsB : Inputs () :=
  preludeInputsFor 1

noncomputable def combinedInputsB : CombinedInputs () where
  toInputs := preludeInputsB
  cold := coldInputs preludeInputsB.stage64

noncomputable def profile : Profile Unit where
  registration.inputs := fun previous => by
    cases previous
    exact preludeInputs

noncomputable def combinedProfile : CombinedProfile Unit where
  registration.inputs := fun previous => by
    cases previous
    exact combinedInputs

noncomputable def combinedProfileB : CombinedProfile Unit where
  registration.inputs := fun previous => by
    cases previous
    exact combinedInputsB

noncomputable def standaloneResult := profile.execution.run ()
noncomputable def combinedResult := combinedProfile.execution.run ()
noncomputable def typeAResult := combinedProfile.typeABExecution.run ()
noncomputable def typeBResult := combinedProfileB.typeABExecution.run ()

example : profile.execution.checks () = 8 := by rfl
example : profile.execution.work () = 8 := by rfl
example : combinedProfile.execution.checks () = 28 := by rfl
example : combinedProfile.execution.work () = 28 := by rfl
example : combinedProfile.typeABExecution.checks () = 29 := by rfl
example : combinedProfile.typeABExecution.work () = 29 := by rfl

example :
    combinedProfile.typeABExecution.terminal () typeAResult =
      .typeA := by rfl
example :
    combinedProfileB.typeABExecution.terminal () typeBResult =
      .typeB := by rfl
example :
    (combinedProfile.typeAProofQuery?) typeAResult |>.isSome := by
  rfl
example :
    (combinedProfile.typeBProofQuery?) typeAResult = none := by
  rfl
example :
    (combinedProfileB.typeAProofQuery?) typeBResult = none := by
  rfl
example :
    (combinedProfileB.typeBProofQuery?) typeBResult |>.isSome := by
  rfl

/-! Every node-57--64 fact remains directly queryable from the classified
residual; consumers never traverse the predecessor chain. -/
example : combinedProfile.netAtTypeABQuery typeAResult = () := by rfl
example : combinedProfile.chargeAtTypeABQuery typeAResult = () := by rfl
example :
    combinedProfile.node59AtTypeABQuery typeAResult =
      .noBranch (by decide) := by
  rfl
example : combinedProfile.closedAtTypeABQuery typeAResult = () := by rfl
example :
    combinedProfile.componentAtTypeABQuery typeAResult = () := by
  rfl
example :
    match combinedProfile.node62AtTypeABQuery typeAResult with
    | .above _ => False
    | .atOrBelow _ => True := by
  trivial
example : combinedProfile.handoffAtTypeABQuery typeAResult = () := by rfl
example :
    combinedProfile.node64ResidualAtTypeABQuery typeAResult = () := by
  rfl

/-! The twenty cold-branch facts are likewise read directly from the
framework-owned Type-A branch stage. -/
example :
    combinedProfile.interface145AtTypeABQuery typeAResult = () := by
  rfl
example :
    match combinedProfile.decision146AtTypeABQuery typeAResult with
    | .yesBranch _ => False
    | .noBranch _ => True := by
  trivial
example : combinedProfile.route147AtTypeABQuery typeAResult = () := by rfl
example :
    combinedProfile.private148AtTypeABQuery typeAResult = () := by
  rfl
example : combinedProfile.audit149AtTypeABQuery typeAResult = () := by rfl
example : combinedProfile.cold150AtTypeABQuery typeAResult = () := by rfl
example :
    combinedProfile.filter151AtTypeABQuery typeAResult = () := by
  rfl
example : combinedProfile.stubs152AtTypeABQuery typeAResult = () := by rfl
example : combinedProfile.scan153AtTypeABQuery typeAResult = () := by rfl
example :
    match combinedProfile.decision154AtTypeABQuery typeAResult with
    | .yesBranch _ => False
    | .noBranch _ => True := by
  trivial
example :
    combinedProfile.certificate155AtTypeABQuery typeAResult = () := by
  rfl
example :
    match combinedProfile.decision156AtTypeABQuery typeAResult with
    | .yesBranch _ => True
    | .noBranch _ => False := by
  trivial
example : combinedProfile.germ157AtTypeABQuery typeAResult = () := by rfl
example : True := by
  have _bounded := combinedProfile.bounded158AtTypeABQuery typeAResult
  trivial
example : True := by
  have _witness := combinedProfile.witness159AtTypeABQuery typeAResult
  trivial
example :
    match combinedProfile.decision160AtTypeABQuery typeAResult with
    | .yesBranch _ => True
    | .noBranch _ => False := by
  trivial
example :
    combinedProfile.evidence161AtTypeABQuery typeAResult = () := by
  rfl
example :
    combinedProfile.residual162AtTypeABQuery typeAResult = () := by
  rfl
example :
    combinedProfile.package163AtTypeABQuery typeAResult = () := by
  rfl
example :
    combinedProfile.package164AtTypeABQuery typeAResult = () := by
  rfl

#check Profile.residualQuery
#check CombinedProfile.residualQuery
#check combinedResult

end Hypostructure.Fixtures.ColdBranchPreludeAggregation
