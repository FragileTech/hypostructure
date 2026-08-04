import Hypostructure.Core.Budget.Dynamic
import Hypostructure.Core.OrderThresholdSplit
import Hypostructure.Core.Residual.Ledger
import Hypostructure.Core.Strategy
import Hypostructure.Core.Strategy.ColdBranchAggregation
import Hypostructure.Core.Strategy.ScaleThresholdDichotomy
import Hypostructure.Graph.SupportComponents

/-!
# Cold-branch prelude aggregation

Direct aggregation of the transitions formerly written as nodes 57--64.
This module imports none of those application node files and returns their
last residual without claiming closure.
-/

namespace Hypostructure.Graph.Strategy.ColdBranchPreludeAggregation

open Hypostructure

universe u v

abbrev Stage57 (Previous : Type u) (Net : Previous → Type v) :=
  Core.Residual.Ledger.Extension Previous Net

noncomputable def step57 (previous : Previous)
    (Net : Previous → Type v) (net : Net previous) :
    Stage57 Previous Net :=
  Core.Residual.Ledger.extend previous net

def netQuery :
    Core.Residual.Query (Stage57 Previous Net)
      (fun stage => Net stage.previous) :=
  Core.Residual.Query.latest

structure ChargeContract (Previous : Type u) (Quantity : Type v)
    [Preorder Quantity] where
  profile : Core.Budget.Dynamic.Profile Previous Quantity

theorem chargeWithin [Preorder Quantity]
    (contract : ChargeContract Previous Quantity) (previous : Previous) :
    contract.profile.current previous ≤ contract.profile.limit previous :=
  contract.profile.current_le_limit previous

abbrev Stage58 (Previous : Type u) (Charge : Previous → Type v) :=
  Core.Residual.Ledger.Extension Previous Charge

noncomputable def step58 (previous : Previous)
    (Charge : Previous → Type v) (charge : Charge previous) :
    Stage58 Previous Charge :=
  Core.Residual.Ledger.extend previous charge

def chargeQuery :
    Core.Residual.Query (Stage58 Previous Charge)
      (fun stage => Charge stage.previous) :=
  Core.Residual.Query.latest

structure Contract59 (Previous : Type u) where
  profile : Previous → Core.OrderThresholdSplit.Profile Nat

abbrev Nonnegative59 (contract : Contract59 Previous)
    (stage : Previous) : Prop :=
  (contract.profile stage).threshold < (contract.profile stage).value

abbrev Negative59 (contract : Contract59 Previous)
    (stage : Previous) : Prop :=
  (contract.profile stage).value ≤ (contract.profile stage).threshold

abbrev Stage59 (contract : Contract59 Previous) :=
  Core.Residual.Decision.Stage (Nonnegative59 contract) (Negative59 contract)

noncomputable def step59 (contract : Contract59 Previous)
    (previous : Previous) : Stage59 contract :=
  let decision : Core.Residual.Decision.Node _
      (Nonnegative59 contract) (Negative59 contract) :=
    Core.Residual.Decision.Node.create
      (fun _ => by classical exact inferInstance)
      (fun _ absent => le_of_not_gt absent)
  decision.run previous

def decision59Query :
    Core.Residual.Query (Stage59 contract)
      (fun stage => Core.Residual.Decision.Binary
        (Nonnegative59 contract) (Negative59 contract) stage.previous) :=
  Core.Residual.Query.latest

structure ClosureContract (Previous : Type u)
    (Nonnegative : Previous → Prop) where
  nonnegative : ∀ previous, Nonnegative previous
  contradiction : ∀ previous, Nonnegative previous → False

theorem close (contract : ClosureContract Previous Nonnegative)
    (previous : Previous) : False :=
  contract.contradiction previous (contract.nonnegative previous)

abbrev Stage60 (Previous : Type u) (Closed : Previous → Type v) :=
  Core.Residual.Ledger.Extension Previous Closed

noncomputable def step60 (previous : Previous)
    (Closed : Previous → Type v) (closed : Closed previous) :
    Stage60 Previous Closed :=
  Core.Residual.Ledger.extend previous closed

def closedQuery :
    Core.Residual.Query (Stage60 Previous Closed)
      (fun stage => Closed stage.previous) :=
  Core.Residual.Query.latest

structure ComponentContract (Previous : Type u)
    (Vertex : Previous → Type v) where
  object : Core.Residual.Query Previous (fun _ => Graph.FiniteObject.{v})
  support : Core.Residual.Query Previous (fun previous =>
    Finset (object.read previous).Vertex)

abbrev Components (contract : ComponentContract Previous Vertex)
    (previous : Previous) :=
  List (Graph.SupportComponents.Connected.Component
    (contract.object.read previous) (contract.support.read previous))

noncomputable def components
    (contract : ComponentContract Previous Vertex) (previous : Previous) :
    Core.Residual.Ledger.Extension Previous (Components contract) :=
  Core.Residual.Ledger.extend previous
    (Graph.SupportComponents.Connected.order
      (contract.object.read previous) (contract.support.read previous))

abbrev Stage61 (Previous : Type u) (Component : Previous → Type v) :=
  Core.Residual.Ledger.Extension Previous Component

noncomputable def step61 (previous : Previous)
    (Component : Previous → Type v) (component : Component previous) :
    Stage61 Previous Component :=
  Core.Residual.Ledger.extend previous component

def componentQuery :
    Core.Residual.Query (Stage61 Previous Component)
      (fun stage => Component stage.previous) :=
  Core.Residual.Query.latest

structure Contract62 (Previous : Type u) where
  profile : Previous → Core.OrderThresholdSplit.Profile Nat

def Contract62.comparison (contract : Contract62 Previous) :
    Core.Residual.Query Previous fun _ =>
      Core.OrderThresholdSplit.Profile Nat :=
  Core.Residual.Query.ofFunction contract.profile

def Contract62.ctProfile (contract : Contract62 Previous) :
    Core.Strategy.ScaleThresholdDichotomy.Profile Previous :=
  Core.Strategy.ScaleThresholdDichotomy.Profile.ofComparisonQuery
    contract.comparison

abbrev Stage62 (contract : Contract62 Previous) :=
  Core.Residual.Ledger.Extension Previous
    (contract.ctProfile.RoutedResidual)

noncomputable def step62 (contract : Contract62 Previous)
    (previous : Previous) : Stage62 contract :=
  Core.Residual.Ledger.extend previous (contract.ctProfile.route previous)

def threshold62Query :
    Core.Residual.Query (Stage62 contract)
      (fun stage => contract.ctProfile.RoutedResidual stage.previous) :=
  Core.Residual.Query.latest

structure BridgeContract (Previous : Type u)
    (Handoff : Previous → Type v) where
  produce : (previous : Previous) → Handoff previous

abbrev Stage63 (Previous : Type u) (Handoff : Previous → Type v) :=
  Core.Residual.Ledger.Extension Previous Handoff

noncomputable def step63 (previous : Previous)
    (Handoff : Previous → Type v) (handoff : Handoff previous) :
    Stage63 Previous Handoff :=
  Core.Residual.Ledger.extend previous handoff

def handoffQuery :
    Core.Residual.Query (Stage63 Previous Handoff)
      (fun stage => Handoff stage.previous) :=
  Core.Residual.Query.latest

noncomputable def step63FromContract
    (contract : BridgeContract Previous Handoff) (previous : Previous) :
    Stage63 Previous Handoff :=
  step63 previous Handoff (contract.produce previous)

structure ResidualContract (Previous : Type u)
    (Residual : Previous → Type v) where
  produce : (previous : Previous) → Residual previous

abbrev Stage64 (Previous : Type u) (Residual : Previous → Type v) :=
  Core.Residual.Ledger.Extension Previous Residual

noncomputable def step64 (previous : Previous)
    (Residual : Previous → Type v) (residual : Residual previous) :
    Stage64 Previous Residual :=
  Core.Residual.Ledger.extend previous residual

def node64ResidualQuery :
    Core.Residual.Query (Stage64 Previous Residual)
      (fun stage => Residual stage.previous) :=
  Core.Residual.Query.latest

noncomputable def step64FromContract
    (contract : ResidualContract Previous Residual) (previous : Previous) :
    Stage64 Previous Residual :=
  step64 previous Residual (contract.produce previous)

/-! ## Standalone node-57--64 strategy -/

structure Inputs {Previous : Type u} (previous : Previous) where
  Net : Previous → Type u
  net : Net previous
  Charge : Stage57 Previous Net → Type u
  charge : Charge (step57 previous Net net)
  contract59 : Contract59 (Stage58 (Stage57 Previous Net) Charge)
  Closed : Stage59 contract59 → Type u
  closed : Closed (step59 contract59
    (step58 (step57 previous Net net) Charge charge))
  Component :
    Stage60 (Stage59 contract59) Closed → Type u
  component : Component (step60
    (step59 contract59 (step58 (step57 previous Net net) Charge charge))
    Closed closed)
  contract62 : Contract62
    (Stage61 (Stage60 (Stage59 contract59) Closed) Component)
  Handoff : Stage62 contract62 → Type u
  handoff : Handoff (step62 contract62 (step61
    (step60
      (step59 contract59 (step58 (step57 previous Net net) Charge charge))
      Closed closed)
    Component component))
  Residual : Stage63 (Stage62 contract62) Handoff → Type u
  residual : Residual (step63
    (step62 contract62 (step61
      (step60
        (step59 contract59 (step58 (step57 previous Net net) Charge charge))
        Closed closed)
      Component component))
    Handoff handoff)

namespace Inputs

variable {Previous : Type u} {previous : Previous}

noncomputable def stage57 (input : Inputs previous) :=
  step57 previous input.Net input.net

noncomputable def stage58 (input : Inputs previous) :=
  step58 input.stage57 input.Charge input.charge

noncomputable def stage59 (input : Inputs previous) :=
  step59 input.contract59 input.stage58

noncomputable def stage60 (input : Inputs previous) :=
  step60 input.stage59 input.Closed input.closed

noncomputable def stage61 (input : Inputs previous) :=
  step61 input.stage60 input.Component input.component

noncomputable def stage62 (input : Inputs previous) :=
  step62 input.contract62 input.stage61

noncomputable def stage63 (input : Inputs previous) :=
  step63 input.stage62 input.Handoff input.handoff

noncomputable def stage64 (input : Inputs previous) :=
  step64 input.stage63 input.Residual input.residual

/-- Preserve the node-57 net fact through the complete prelude. -/
def netAt64Query (input : Inputs previous) :=
  let q58 := (netQuery (Net := input.Net)).preserve (Added := input.Charge)
  let q59 := q58.preserve (Added :=
    Core.Residual.Decision.Binary
      (Nonnegative59 input.contract59) (Negative59 input.contract59))
  let q60 := q59.preserve (Added := input.Closed)
  let q61 := q60.preserve (Added := input.Component)
  let q62 := q61.preserve (Added :=
    input.contract62.ctProfile.RoutedResidual)
  let q63 := q62.preserve (Added := input.Handoff)
  q63.preserve (Added := input.Residual)

/-- Preserve the node-58 charge fact through the complete prelude. -/
def chargeAt64Query (input : Inputs previous) :=
  let q59 := (chargeQuery (Charge := input.Charge)).preserve (Added :=
    Core.Residual.Decision.Binary
      (Nonnegative59 input.contract59) (Negative59 input.contract59))
  let q60 := q59.preserve (Added := input.Closed)
  let q61 := q60.preserve (Added := input.Component)
  let q62 := q61.preserve (Added :=
    input.contract62.ctProfile.RoutedResidual)
  let q63 := q62.preserve (Added := input.Handoff)
  q63.preserve (Added := input.Residual)

/-- Preserve the node-59 decision through the complete prelude. -/
def node59At64Query (input : Inputs previous) :=
  let q60 :=
    (decision59Query (contract := input.contract59)).preserve
      (Added := input.Closed)
  let q61 := q60.preserve (Added := input.Component)
  let q62 := q61.preserve (Added :=
    input.contract62.ctProfile.RoutedResidual)
  let q63 := q62.preserve (Added := input.Handoff)
  q63.preserve (Added := input.Residual)

/-- Preserve the node-60 closure fact through the complete prelude. -/
def closedAt64Query (input : Inputs previous) :=
  let q61 := (closedQuery (Closed := input.Closed)).preserve
    (Added := input.Component)
  let q62 := q61.preserve (Added :=
    input.contract62.ctProfile.RoutedResidual)
  let q63 := q62.preserve (Added := input.Handoff)
  q63.preserve (Added := input.Residual)

/-- Preserve the node-61 component fact through the complete prelude. -/
def componentAt64Query (input : Inputs previous) :=
  let q62 := (componentQuery (Component := input.Component)).preserve (Added :=
    input.contract62.ctProfile.RoutedResidual)
  let q63 := q62.preserve (Added := input.Handoff)
  q63.preserve (Added := input.Residual)

/-- Preserve the exact node-62 decision query through nodes 63 and 64. -/
def node62At64Query (input : Inputs previous) :=
  let q63 :=
    (threshold62Query (contract := input.contract62)).preserve
      (Added := input.Handoff)
  q63.preserve (Added := input.Residual)

/-- Preserve the node-63 handoff fact through node 64. -/
def handoffAt64Query (input : Inputs previous) :=
  (handoffQuery (Handoff := input.Handoff)).preserve (Added := input.Residual)

/-- Read the node-64 residual from the complete prelude. -/
def residualAt64Query (input : Inputs previous) :=
  node64ResidualQuery (Residual := input.Residual)

end Inputs

structure Registration (Previous : Type u) where
  inputs : Core.Residual.Query Previous (fun previous => Inputs previous)

structure Profile (Previous : Type u) where
  registration : Registration Previous

namespace Profile

variable (profile : Profile Previous)

inductive Phase
  | n57 | n58 | n59 | n60 | n61 | n62 | n63 | n64
  deriving DecidableEq, Fintype

noncomputable def execution : Core.Strategy.CTExecution Previous where
  Terminal := Core.Strategy.CompletedTerminal
  Output := fun previous =>
    let input := profile.registration.inputs.read previous
    Stage64
      (Stage63 (Stage62 input.contract62) input.Handoff)
      input.Residual
  run := fun previous => (profile.registration.inputs.read previous).stage64
  terminal := fun _ _ => .completed
  checks := fun _ => Fintype.card Phase
  work := fun _ => Fintype.card Phase

/-- The literal predecessor consumed by this profile.  This is an identity
query, so the strategy cannot be run against a reconstructed stage. -/
def inputResidualQuery :
    Core.Residual.Query Previous (fun _ => Previous) :=
  Core.Residual.Query.ofFunction id

/- The exact residual-producing output of the registered execution. -/
noncomputable def outputResidual (profile : Profile Previous)
    (previous : Previous) : profile.execution.Output previous :=
  profile.execution.run previous

def residualQuery :
    Core.Residual.Query (profile.execution.Output previous)
      (fun _ => profile.execution.Output previous) :=
  Core.Residual.Query.ofFunction id

end Profile

/-! ## Typed continuation through nodes 145--164 -/

structure CombinedInputs {Previous : Type u} (previous : Previous)
    extends Inputs previous where
  cold :
    Hypostructure.Core.Strategy.ColdBranchAggregation.Inputs
      toInputs.stage64

structure CombinedRegistration (Previous : Type u) where
  inputs :
    Core.Residual.Query Previous (fun previous => CombinedInputs previous)

namespace CombinedRegistration

/-! The combined fixture carries a prelude input whose cold payload is indexed
by `toInputs.stage64`.  Framework registrations, however, are invoked after
the prelude and therefore must be indexed by that literal stage-64 residual.
Keep that registration boundary separate from the fixture wrapper. -/
structure Stage64Registration (Previous : Type u) where
  inputs : Core.Residual.Query Previous
    (fun previous =>
      Core.Strategy.ColdBranchAggregation.Inputs previous)

def coldBranchAggregation
    (registration : Stage64Registration Previous) :
    Core.Strategy.ColdBranchAggregation.Registration Previous where
  inputs := registration.inputs

def finiteStateNetChargeContinuation
    {Residual : Type u} {Target : Residual → Prop}
    (registration :
      Core.Strategy.FiniteStateNetChargeContinuation.Registration
        Residual Target) :
    Core.Strategy.FiniteStateNetChargeContinuation.Registration
      Residual Target :=
  registration

end CombinedRegistration

structure CombinedProfile (Previous : Type u) where
  registration : CombinedRegistration Previous

namespace CombinedProfile

variable (profile : CombinedProfile Previous)

noncomputable def execution : Core.Strategy.CTExecution Previous where
  Terminal := Core.Strategy.CompletedTerminal
  Output := fun previous =>
    let input := profile.registration.inputs.read previous
    Hypostructure.Core.Strategy.ColdBranchAggregation.Stage164
      (Hypostructure.Core.Strategy.ColdBranchAggregation.Stage163
        input.cold.contract163)
      input.cold.Package
  run := fun previous =>
    (profile.registration.inputs.read previous).cold.stage164
  terminal := fun _ _ => .completed
  checks := fun _ =>
    Fintype.card Profile.Phase +
      Fintype.card
        Hypostructure.Core.Strategy.ColdBranchAggregation.Profile.Phase
  work := fun _ =>
    Fintype.card Profile.Phase +
      Fintype.card
        Hypostructure.Core.Strategy.ColdBranchAggregation.Profile.Phase

def inputResidualQuery :
    Core.Residual.Query Previous (fun _ => Previous) :=
  Core.Residual.Query.ofFunction id

noncomputable def outputResidual (profile : CombinedProfile Previous)
    (previous : Previous) : profile.execution.Output previous :=
  profile.execution.run previous

def residualQuery :
    Core.Residual.Query (profile.execution.Output previous)
      (fun _ => profile.execution.Output previous) :=
  Core.Residual.Query.ofFunction id

/-- Read the literal node-62 decision retained inside the final node-164
ledger.  This is the framework-native replacement for reconstructing the
named node chain in the application. -/
noncomputable def threshold62Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.preservePrevious input.toInputs.node62At64Query

noncomputable def netQuery {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.preservePrevious input.toInputs.netAt64Query

noncomputable def chargeQuery {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.preservePrevious input.toInputs.chargeAt64Query

noncomputable def node59Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.preservePrevious input.toInputs.node59At64Query

noncomputable def closedQuery {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.preservePrevious input.toInputs.closedAt64Query

noncomputable def componentQuery {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.preservePrevious input.toInputs.componentAt64Query

noncomputable def handoffQuery {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.preservePrevious input.toInputs.handoffAt64Query

noncomputable def node64ResidualQuery {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.preservePrevious input.toInputs.residualAt64Query

noncomputable def interface145Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.interfaceAt164Query

noncomputable def decision146Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.decision146At164Query

noncomputable def route147Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.routeAt164Query

noncomputable def private148Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.privateAt164Query

noncomputable def audit149Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.auditAt164Query

noncomputable def cold150Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.coldAt164Query

noncomputable def filter151Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.filterAt164Query

noncomputable def stubs152Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.stubsAt164Query

noncomputable def scan153Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.scanAt164Query

noncomputable def decision154Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.decision154At164Query

noncomputable def certificate155Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.certificateAt164Query

noncomputable def decision156Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.decision156At164Query

noncomputable def germ157Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.germAt164Query

noncomputable def bounded158Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.bounded158At164Query

noncomputable def witness159Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.witness159At164Query

noncomputable def decision160Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.decision160At164Query

noncomputable def evidence161Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.evidenceAt164Query

noncomputable def residual162Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.residual162At164Query

noncomputable def package163Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.package163At164Query

noncomputable def package164Query {previous : Previous} :=
  let input := profile.registration.inputs.read previous
  input.cold.package164At164Query

inductive TypeABTerminal
  | typeA
  | typeB
  deriving DecidableEq, Repr, Fintype

inductive RoutePhase
  | classify
  deriving DecidableEq, Fintype

/-- Classify the retained decision without recomputing its threshold. -/
noncomputable def typeABClassificationQuery {previous : Previous} :
    Core.Residual.Query (profile.execution.Output previous)
      (fun _ => TypeABTerminal) :=
  (profile.threshold62Query (previous := previous)).map fun _ decision =>
    match decision with
    | .above _ => .typeB
    | .atOrBelow _ => .typeA

/-- The framework-owned dichotomy at the literal node-164 residual.  Its
classification is exactly the retained node-62 decision; neither branch
proof is recomputed. -/
noncomputable def typeABDichotomy (previous : Previous) :
    Core.Strategy.Dichotomy (profile.execution.Output previous) where
  LeftPayload := fun final =>
    Core.Strategy.ProofPayload
      (profile.typeABClassificationQuery.read final = .typeA)
  RightPayload := fun final =>
    Core.Strategy.ProofPayload
      (profile.typeABClassificationQuery.read final = .typeB)
  classify final :=
    match profile.typeABClassificationQuery.read final with
    | .typeA => .inl ⟨rfl⟩
    | .typeB => .inr ⟨rfl⟩

/-- Framework-native migration of `only_type_A_or_B`: execute the migrated
residual transformation and let Core's canonical dichotomy runner append the
exact retained branch proof to the literal node-164 residual. -/
noncomputable def typeABExecution :
    Core.Strategy.CTExecution Previous where
  Terminal := TypeABTerminal
  Output := fun previous =>
    Core.Strategy.DichotomyStage (profile.typeABDichotomy previous)
  run := fun previous =>
    let final := profile.execution.run previous
    Core.Strategy.runDichotomy (profile.typeABDichotomy previous) final
  terminal := fun _ output =>
    match output with
    | .inl _ => .typeA
    | .inr _ => .typeB
  checks := fun previous =>
    profile.execution.checks previous + Fintype.card RoutePhase
  work := fun previous =>
    profile.execution.work previous + Fintype.card RoutePhase

def typeABOutcomeQuery :
    Core.Residual.Query (profile.typeABExecution.Output previous)
      (fun _ => TypeABTerminal) :=
  Core.Residual.Query.ofFunction fun output =>
    match output with
    | Sum.inl _ => .typeA
    | Sum.inr _ => .typeB

/-- Preserve any fact queryable at node 164 through the Type A/B outcome
extension. -/
def preserveThroughTypeAB
    {previous : Previous}
    {Result : profile.execution.Output previous → Sort v}
    (query : Core.Residual.Query (profile.execution.Output previous) Result) :
    Core.Residual.Query (profile.typeABExecution.Output previous)
      (fun output =>
        match output with
        | Sum.inl stage => Result stage.previous
        | Sum.inr stage => Result stage.previous) :=
  Core.Residual.Query.ofFunction fun output =>
    match output with
    | Sum.inl stage => query.preserve.read stage
    | Sum.inr stage => query.preserve.read stage

noncomputable def node62AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.threshold62Query (previous := previous))

noncomputable def netAtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.netQuery (previous := previous))

noncomputable def chargeAtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.chargeQuery (previous := previous))

noncomputable def node59AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.node59Query (previous := previous))

noncomputable def closedAtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.closedQuery (previous := previous))

noncomputable def componentAtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.componentQuery (previous := previous))

noncomputable def handoffAtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.handoffQuery (previous := previous))

noncomputable def node64ResidualAtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.node64ResidualQuery (previous := previous))

noncomputable def interface145AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.interface145Query (previous := previous))

noncomputable def decision146AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.decision146Query (previous := previous))

noncomputable def route147AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.route147Query (previous := previous))

noncomputable def private148AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.private148Query (previous := previous))

noncomputable def audit149AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.audit149Query (previous := previous))

noncomputable def cold150AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.cold150Query (previous := previous))

noncomputable def filter151AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.filter151Query (previous := previous))

noncomputable def stubs152AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.stubs152Query (previous := previous))

noncomputable def scan153AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.scan153Query (previous := previous))

noncomputable def decision154AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.decision154Query (previous := previous))

noncomputable def certificate155AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.certificate155Query (previous := previous))

noncomputable def decision156AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.decision156Query (previous := previous))

noncomputable def germ157AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.germ157Query (previous := previous))

noncomputable def bounded158AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.bounded158Query (previous := previous))

noncomputable def witness159AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.witness159Query (previous := previous))

noncomputable def decision160AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.decision160Query (previous := previous))

noncomputable def evidence161AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.evidence161Query (previous := previous))

noncomputable def residual162AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.residual162Query (previous := previous))

noncomputable def package163AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.package163Query (previous := previous))

noncomputable def package164AtTypeABQuery {previous : Previous} :=
  profile.preserveThroughTypeAB
    (profile.package164Query (previous := previous))

def typeAProofQuery? :
    Core.Residual.Query (profile.typeABExecution.Output previous)
      (fun output =>
        Option (Core.Strategy.ProofPayload
          (profile.typeABOutcomeQuery.read output = .typeA))) :=
  Core.Residual.Query.ofFunction fun output =>
    match output with
    | Sum.inl _ => some ⟨rfl⟩
    | Sum.inr _ => none

def typeBProofQuery? :
    Core.Residual.Query (profile.typeABExecution.Output previous)
      (fun output =>
        Option (Core.Strategy.ProofPayload
          (profile.typeABOutcomeQuery.read output = .typeB))) :=
  Core.Residual.Query.ofFunction fun output =>
    match output with
    | Sum.inl _ => none
    | Sum.inr _ => some ⟨rfl⟩

end CombinedProfile

end Hypostructure.Graph.Strategy.ColdBranchPreludeAggregation
