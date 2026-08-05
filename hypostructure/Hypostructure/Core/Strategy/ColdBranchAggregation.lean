import Hypostructure.Core.OrderThresholdSplit
import Hypostructure.Core.Strategy.Execution
import Hypostructure.Core.Strategy.ColdBranchAggregationSemantics
import Hypostructure.Core.Strategy.FiniteBarrierEnumerationSemantics

/-!
# Cold-branch aggregation

This module is a direct aggregation of the transitions formerly written as
nodes 145--164.  It deliberately does not import those node modules and does
not close the residual produced by the last transition.
-/

namespace Hypostructure.Core.Strategy.ColdBranchAggregation

open Hypostructure

universe u v uResidual uPacking uClosure uOwner uItem uState uOutput

abbrev Stage145 (Previous : Type u) (Interface : Previous → Type v) :=
  Core.Residual.Ledger.Extension Previous Interface

noncomputable def step145 (previous : Previous)
    (Interface : Previous → Type v) (interface : Interface previous) :
    Stage145 Previous Interface :=
  Core.Residual.Ledger.extend previous interface

def interfaceQuery :
    Core.Residual.Query (Stage145 Previous Interface)
      (fun stage => Interface stage.previous) :=
  Core.Residual.Query.latest

structure Contract146 (Previous : Type u) where
  profile : Previous → Core.OrderThresholdSplit.Profile Nat

abbrev Below146 (contract : Contract146 Previous) (stage : Previous) : Prop :=
  (contract.profile stage).threshold < (contract.profile stage).value

abbrev AtMost146 (contract : Contract146 Previous) (stage : Previous) : Prop :=
  (contract.profile stage).value ≤ (contract.profile stage).threshold

abbrev Stage146 (contract : Contract146 Previous) :=
  Core.Residual.Decision.Stage (Below146 contract) (AtMost146 contract)

noncomputable def step146 (contract : Contract146 Previous)
    (previous : Previous) : Stage146 contract :=
  let decision : Core.Residual.Decision.Node _
      (Below146 contract) (AtMost146 contract) :=
    Core.Residual.Decision.Node.create
      (fun _ => by classical exact inferInstance)
      (fun _ absent => le_of_not_gt absent)
  decision.run previous

def decision146Query :
    Core.Residual.Query (Stage146 contract)
      (fun stage => Core.Residual.Decision.Binary
        (Below146 contract) (AtMost146 contract) stage.previous) :=
  Core.Residual.Query.latest

abbrev Stage147 (Previous : Type u) (Route : Previous → Type v) :=
  Core.Residual.Ledger.Extension Previous Route

noncomputable def step147 (previous : Previous)
    (Route : Previous → Type v) (route : Route previous) :
    Stage147 Previous Route :=
  Core.Residual.Ledger.extend previous route

def routeQuery :
    Core.Residual.Query (Stage147 Previous Route)
      (fun stage => Route stage.previous) :=
  Core.Residual.Query.latest

abbrev Stage148 (Previous : Type u) (Private : Previous → Type v) :=
  Core.Residual.Ledger.Extension Previous Private

noncomputable def step148 (previous : Previous)
    (Private : Previous → Type v) (privateData : Private previous) :
    Stage148 Previous Private :=
  Core.Residual.Ledger.extend previous privateData

def privateQuery :
    Core.Residual.Query (Stage148 Previous Private)
      (fun stage => Private stage.previous) :=
  Core.Residual.Query.latest

abbrev Stage149 (Previous : Type u) (Audit : Previous → Type v) :=
  Core.Residual.Ledger.Extension Previous Audit

noncomputable def step149 (previous : Previous)
    (Audit : Previous → Type v) (audit : Audit previous) :
    Stage149 Previous Audit :=
  Core.Residual.Ledger.extend previous audit

def auditQuery :
    Core.Residual.Query (Stage149 Previous Audit)
      (fun stage => Audit stage.previous) :=
  Core.Residual.Query.latest

abbrev Stage150 (Previous : Type u) (Cold : Previous → Type v) :=
  Core.Residual.Ledger.Extension Previous Cold

noncomputable def step150 (previous : Previous)
    (Cold : Previous → Type v) (cold : Cold previous) :
    Stage150 Previous Cold :=
  Core.Residual.Ledger.extend previous cold

def coldQuery :
    Core.Residual.Query (Stage150 Previous Cold)
      (fun stage => Cold stage.previous) :=
  Core.Residual.Query.latest

abbrev Stage151 (Previous : Type u) (Filter : Previous → Type v) :=
  Core.Residual.Ledger.Extension Previous Filter

noncomputable def step151 (previous : Previous)
    (Filter : Previous → Type v) (filter : Filter previous) :
    Stage151 Previous Filter :=
  Core.Residual.Ledger.extend previous filter

def filterQuery {Previous : Type u} {Filter : Previous → Type v} :
    Core.Residual.Query (Stage151 Previous Filter)
      (fun stage => Filter stage.previous) :=
  Core.Residual.Query.latest

abbrev Stage152 (Previous : Type u) (Stubs : Previous → Type v) :=
  Core.Residual.Ledger.Extension Previous Stubs

noncomputable def step152 (previous : Previous)
    (Stubs : Previous → Type v) (stubs : Stubs previous) :
    Stage152 Previous Stubs :=
  Core.Residual.Ledger.extend previous stubs

def stubsQuery :
    Core.Residual.Query (Stage152 Previous Stubs)
      (fun stage => Stubs stage.previous) :=
  Core.Residual.Query.latest

abbrev Stage153 (Previous : Type u) (Scan : Previous → Type v) :=
  Core.Residual.Ledger.Extension Previous Scan

noncomputable def step153 (previous : Previous)
    (Scan : Previous → Type v) (scan : Scan previous) :
    Stage153 Previous Scan :=
  Core.Residual.Ledger.extend previous scan

def scanQuery :
    Core.Residual.Query (Stage153 Previous Scan)
      (fun stage => Scan stage.previous) :=
  Core.Residual.Query.latest

structure Contract154 (Previous : Type u) where
  profile : Previous → Core.OrderThresholdSplit.Profile Nat

abbrev Hit154 (contract : Contract154 Previous) (stage : Previous) : Prop :=
  (contract.profile stage).threshold < (contract.profile stage).value

abbrev NoHit154 (contract : Contract154 Previous) (stage : Previous) : Prop :=
  (contract.profile stage).value ≤ (contract.profile stage).threshold

abbrev Stage154 (contract : Contract154 Previous) :=
  Core.Residual.Decision.Stage (Hit154 contract) (NoHit154 contract)

noncomputable def step154 (contract : Contract154 Previous)
    (previous : Previous) : Stage154 contract :=
  let decision : Core.Residual.Decision.Node _
      (Hit154 contract) (NoHit154 contract) :=
    Core.Residual.Decision.Node.create
      (fun _ => by classical exact inferInstance)
      (fun _ absent => le_of_not_gt absent)
  decision.run previous

def decision154Query :
    Core.Residual.Query (Stage154 contract)
      (fun stage => Core.Residual.Decision.Binary
        (Hit154 contract) (NoHit154 contract) stage.previous) :=
  Core.Residual.Query.latest

abbrev Stage155 (Previous : Type u) (Certificate : Previous → Type v) :=
  Core.Residual.Ledger.Extension Previous Certificate

noncomputable def step155 (previous : Previous)
    (Certificate : Previous → Type v) (certificate : Certificate previous) :
    Stage155 Previous Certificate :=
  Core.Residual.Ledger.extend previous certificate

def certificateQuery :
    Core.Residual.Query (Stage155 Previous Certificate)
      (fun stage => Certificate stage.previous) :=
  Core.Residual.Query.latest

structure Contract156 (Previous : Type u) where
  event : Previous → Prop
  event_decidable : DecidablePred event

abbrev Stage156 (contract : Contract156 Previous) :=
  Core.Residual.Decision.Stage contract.event
    (fun previous => ¬ contract.event previous)

noncomputable def step156 (contract : Contract156 Previous)
    (previous : Previous) : Stage156 contract :=
  Core.Residual.Decision.Node.create contract.event_decidable
    (fun _ absent => absent) |>.run previous

def decision156Query :
    Core.Residual.Query (Stage156 contract)
      (fun stage => Core.Residual.Decision.Binary contract.event
        (fun previous => ¬ contract.event previous) stage.previous) :=
  Core.Residual.Query.latest

abbrev Stage157 (Previous : Type u) (Germ : Previous → Type v) :=
  Core.Residual.Ledger.Extension Previous Germ

noncomputable def step157 (previous : Previous)
    (Germ : Previous → Type v) (germ : Germ previous) :
    Stage157 Previous Germ :=
  Core.Residual.Ledger.extend previous germ

def germQuery :
    Core.Residual.Query (Stage157 Previous Germ)
      (fun stage => Germ stage.previous) :=
  Core.Residual.Query.latest

structure Contract158 (Previous : Type u) where
  scale : Previous → Nat
  bounded : Previous → Prop
  bounded_of_scale : ∀ previous, bounded previous

abbrev Stage158 (contract : Contract158 Previous) :=
  Core.Residual.Ledger.Extension Previous
    (fun previous => contract.bounded previous)

noncomputable def step158 (contract : Contract158 Previous)
    (previous : Previous) : Stage158 contract :=
  Core.Residual.Ledger.extend previous (contract.bounded_of_scale previous)

def bounded158Query :
    Core.Residual.Query (Stage158 contract)
      (fun stage => contract.bounded stage.previous) :=
  Core.Residual.Query.latest

structure Contract159 (Previous : Type u) where
  candidate : Previous → Type v
  admissible : (previous : Previous) → candidate previous → Prop
  witness : ∀ previous, Nonempty (candidate previous)
  witness_admissible : ∀ previous, ∃ candidate, admissible previous candidate

abbrev Stage159 (contract : Contract159 Previous) :=
  Core.Residual.Ledger.Extension Previous
    (fun previous => ∃ candidate, contract.admissible previous candidate)

noncomputable def step159 (contract : Contract159 Previous)
    (previous : Previous) : Stage159 contract :=
  Core.Residual.Ledger.extend previous (contract.witness_admissible previous)

def witness159Query :
    Core.Residual.Query (Stage159 contract)
      (fun stage => ∃ candidate,
        contract.admissible stage.previous candidate) :=
  Core.Residual.Query.latest

structure Contract160 (Previous : Type u) where
  good : Previous → Prop
  good_decidable : DecidablePred good

abbrev Stage160 (contract : Contract160 Previous) :=
  Core.Residual.Decision.Stage contract.good
    (fun previous => ¬ contract.good previous)

noncomputable def step160 (contract : Contract160 Previous)
    (previous : Previous) : Stage160 contract :=
  Core.Residual.Decision.Node.create contract.good_decidable
    (fun _ absent => absent) |>.run previous

def decision160Query :
    Core.Residual.Query (Stage160 contract)
      (fun stage => Core.Residual.Decision.Binary contract.good
        (fun previous => ¬ contract.good previous) stage.previous) :=
  Core.Residual.Query.latest

abbrev Stage161 (Previous : Type u) (Evidence : Previous → Type v) :=
  Core.Residual.Ledger.Extension Previous Evidence

noncomputable def step161 (previous : Previous)
    (Evidence : Previous → Type v) (evidence : Evidence previous) :
    Stage161 Previous Evidence :=
  Core.Residual.Ledger.extend previous evidence

def evidenceQuery :
    Core.Residual.Query (Stage161 Previous Evidence)
      (fun stage => Evidence stage.previous) :=
  Core.Residual.Query.latest

abbrev Stage162 (Previous : Type u) (Residual : Previous → Type v) :=
  Core.Residual.Ledger.Extension Previous Residual

noncomputable def step162 (previous : Previous)
    (Residual : Previous → Type v) (residual : Residual previous) :
    Stage162 Previous Residual :=
  Core.Residual.Ledger.extend previous residual

def residual162Query :
    Core.Residual.Query (Stage162 Previous Residual)
      (fun stage => Residual stage.previous) :=
  Core.Residual.Query.latest

structure Contract163 (Previous : Type u) where
  package : Previous → Type v
  package_of_good : ∀ previous, Nonempty (package previous)

abbrev Stage163 (contract : Contract163 Previous) :=
  Core.Residual.Ledger.Extension Previous contract.package

noncomputable def step163 (contract : Contract163 Previous)
    (previous : Previous) : Stage163 contract :=
  Core.Residual.Ledger.extend previous
    (Classical.choice (contract.package_of_good previous))

def package163Query :
    Core.Residual.Query (Stage163 contract)
      (fun stage => contract.package stage.previous) :=
  Core.Residual.Query.latest

abbrev Stage164 (Previous : Type u) (Package : Previous → Type v) :=
  Core.Residual.Ledger.Extension Previous Package

noncomputable def step164 (previous : Previous)
    (Package : Previous → Type v) (package : Package previous) :
    Stage164 Previous Package :=
  Core.Residual.Ledger.extend previous package

def package164Query :
    Core.Residual.Query (Stage164 Previous Package)
      (fun stage => Package stage.previous) :=
  Core.Residual.Query.latest

/-! ## The aggregated program

The following bundle is only the dependent argument list of the copied node
functions, written in their original order.  Later fields are indexed by the
literal stage produced from earlier fields.
-/

structure Prefix160 {Previous : Type u} (previous : Previous) where
  Interface : Previous → Type u
  interface : Interface previous
  contract146 : Contract146 (Stage145 Previous Interface)
  Route : Stage146 contract146 → Type u
  route : Route (step146 contract146 (step145 previous Interface interface))
  Private : Stage147 (Stage146 contract146) Route → Type u
  privateData : Private (step147
    (step146 contract146 (step145 previous Interface interface)) Route route)
  Audit : Stage148 (Stage147 (Stage146 contract146) Route) Private → Type u
  audit : Audit (step148
    (step147 (step146 contract146 (step145 previous Interface interface))
      Route route)
    Private privateData)
  Cold : Stage149
    (Stage148 (Stage147 (Stage146 contract146) Route) Private) Audit → Type u
  cold : Cold (step149
    (step148
      (step147 (step146 contract146 (step145 previous Interface interface))
        Route route)
      Private privateData)
    Audit audit)
  Filter : Stage150
    (Stage149 (Stage148 (Stage147 (Stage146 contract146) Route) Private) Audit)
    Cold → Type u
  filter : Filter (step150
    (step149
      (step148
        (step147 (step146 contract146 (step145 previous Interface interface))
          Route route)
        Private privateData)
      Audit audit)
    Cold cold)
  Stubs : Stage151
    (Stage150
      (Stage149 (Stage148 (Stage147 (Stage146 contract146) Route) Private) Audit)
      Cold)
    Filter → Type u
  stubs : Stubs (step151
    (step150
      (step149
        (step148
          (step147 (step146 contract146 (step145 previous Interface interface))
            Route route)
          Private privateData)
        Audit audit)
      Cold cold)
    Filter filter)
  Scan : Stage152
    (Stage151
      (Stage150
        (Stage149 (Stage148 (Stage147 (Stage146 contract146) Route) Private) Audit)
        Cold)
      Filter)
    Stubs → Type u
  scan : Scan (step152
    (step151
      (step150
        (step149
          (step148
            (step147 (step146 contract146 (step145 previous Interface interface))
              Route route)
            Private privateData)
          Audit audit)
        Cold cold)
      Filter filter)
    Stubs stubs)
  contract154 : Contract154 (Stage153
    (Stage152
      (Stage151
        (Stage150
          (Stage149
            (Stage148 (Stage147 (Stage146 contract146) Route) Private) Audit)
          Cold)
        Filter)
      Stubs)
    Scan)
  Certificate : Stage154 contract154 → Type u
  certificate : Certificate (step154 contract154 (step153
    (step152
      (step151
        (step150
          (step149
            (step148
              (step147
                (step146 contract146 (step145 previous Interface interface))
                Route route)
              Private privateData)
            Audit audit)
          Cold cold)
        Filter filter)
      Stubs stubs)
    Scan scan))
  contract156 : Contract156 (Stage155 (Stage154 contract154) Certificate)
  Germ : Stage156 contract156 → Type u
  germ : Germ (step156 contract156
    (step155
      (step154 contract154 (step153
        (step152
          (step151
            (step150
              (step149
                (step148
                  (step147
                    (step146 contract146 (step145 previous Interface interface))
                    Route route)
                  Private privateData)
                Audit audit)
              Cold cold)
            Filter filter)
          Stubs stubs)
        Scan scan))
      Certificate certificate))
  contract158 : Contract158 (Stage157 (Stage156 contract156) Germ)
  contract159 : Contract159 (Stage158 contract158)
  contract160 : Contract160 (Stage159 contract159)

namespace Prefix160

variable {Previous : Type u} {previous : Previous}

noncomputable def stage145 (input : Prefix160 previous) :=
  step145 previous input.Interface input.interface

noncomputable def stage146 (input : Prefix160 previous) :=
  step146 input.contract146 input.stage145

noncomputable def stage147 (input : Prefix160 previous) :=
  step147 input.stage146 input.Route input.route

noncomputable def stage148 (input : Prefix160 previous) :=
  step148 input.stage147 input.Private input.privateData

noncomputable def stage149 (input : Prefix160 previous) :=
  step149 input.stage148 input.Audit input.audit

noncomputable def stage150 (input : Prefix160 previous) :=
  step150 input.stage149 input.Cold input.cold

noncomputable def stage151 (input : Prefix160 previous) :=
  step151 input.stage150 input.Filter input.filter

noncomputable def stage152 (input : Prefix160 previous) :=
  step152 input.stage151 input.Stubs input.stubs

noncomputable def stage153 (input : Prefix160 previous) :=
  step153 input.stage152 input.Scan input.scan

noncomputable def stage154 (input : Prefix160 previous) :=
  step154 input.contract154 input.stage153

noncomputable def stage155 (input : Prefix160 previous) :=
  step155 input.stage154 input.Certificate input.certificate

noncomputable def stage156 (input : Prefix160 previous) :=
  step156 input.contract156 input.stage155

noncomputable def stage157 (input : Prefix160 previous) :=
  step157 input.stage156 input.Germ input.germ

noncomputable def stage158 (input : Prefix160 previous) :=
  step158 input.contract158 input.stage157

noncomputable def stage159 (input : Prefix160 previous) :=
  step159 input.contract159 input.stage158

noncomputable def stage160 (input : Prefix160 previous) :=
  step160 input.contract160 input.stage159

end Prefix160

structure Inputs {Previous : Type u} (previous : Previous)
    extends Prefix160 previous where
  Evidence : Stage160 toPrefix160.contract160 → Type u
  evidence : Evidence toPrefix160.stage160
  Residual :
    Stage161 (Stage160 toPrefix160.contract160) Evidence → Type u
  residual : Residual
    (step161 toPrefix160.stage160 Evidence evidence)
  contract163 : Contract163
    (Stage162
      (Stage161 (Stage160 toPrefix160.contract160) Evidence)
      Residual)
  Package : Stage163 contract163 → Type u
  package : Package (step163 contract163
    (step162
      (step161 toPrefix160.stage160 Evidence evidence)
      Residual residual))

namespace Inputs

variable {Previous : Type u} {previous : Previous}

noncomputable def stage161 (input : Inputs previous) :=
  step161 input.toPrefix160.stage160 input.Evidence input.evidence

noncomputable def stage162 (input : Inputs previous) :=
  step162 input.stage161 input.Residual input.residual

noncomputable def stage163 (input : Inputs previous) :=
  step163 input.contract163 input.stage162

noncomputable def stage164 (input : Inputs previous) :=
  step164 input.stage163 input.Package input.package

abbrev S145 (input : Inputs previous) :=
  Stage145 Previous input.Interface
abbrev S146 (input : Inputs previous) := Stage146 input.contract146
abbrev S147 (input : Inputs previous) := Stage147 input.S146 input.Route
abbrev S148 (input : Inputs previous) := Stage148 input.S147 input.Private
abbrev S149 (input : Inputs previous) := Stage149 input.S148 input.Audit
abbrev S150 (input : Inputs previous) := Stage150 input.S149 input.Cold
abbrev S151 (input : Inputs previous) := Stage151 input.S150 input.Filter
abbrev S152 (input : Inputs previous) := Stage152 input.S151 input.Stubs
abbrev S153 (input : Inputs previous) := Stage153 input.S152 input.Scan
abbrev S154 (input : Inputs previous) := Stage154 input.contract154
abbrev S155 (input : Inputs previous) :=
  Stage155 input.S154 input.Certificate
abbrev S156 (input : Inputs previous) := Stage156 input.contract156
abbrev S157 (input : Inputs previous) := Stage157 input.S156 input.Germ
abbrev S158 (input : Inputs previous) := Stage158 input.contract158
abbrev S159 (input : Inputs previous) := Stage159 input.contract159
abbrev S160 (input : Inputs previous) := Stage160 input.contract160
abbrev S161 (input : Inputs previous) :=
  Stage161 input.S160 input.Evidence
abbrev S162 (input : Inputs previous) :=
  Stage162 input.S161 input.Residual
abbrev S163 (input : Inputs previous) := Stage163 input.contract163
abbrev S164 (input : Inputs previous) :=
  Stage164 input.S163 input.Package

/-- Typed suffix transports.  Each definition performs exactly the next
ordinary Core ledger preservation and delegates the remaining suffix. -/
def preserveFrom163 (input : Inputs previous) {Result : input.S163 → Sort v}
    (query : Core.Residual.Query input.S163 Result) :=
  query.preserve (Added := input.Package)

def preserveFrom162 (input : Inputs previous) {Result : input.S162 → Sort v}
    (query : Core.Residual.Query input.S162 Result) :=
  input.preserveFrom163
    (query.preserve (Added := input.contract163.package))

def preserveFrom161 (input : Inputs previous) {Result : input.S161 → Sort v}
    (query : Core.Residual.Query input.S161 Result) :=
  input.preserveFrom162 (query.preserve (Added := input.Residual))

def preserveFrom160 (input : Inputs previous) {Result : input.S160 → Sort v}
    (query : Core.Residual.Query input.S160 Result) :=
  input.preserveFrom161 (query.preserve (Added := input.Evidence))

def preserveFrom159 (input : Inputs previous) {Result : input.S159 → Sort v}
    (query : Core.Residual.Query input.S159 Result) :=
  input.preserveFrom160 (query.preserve (Added :=
    Core.Residual.Decision.Binary input.contract160.good
      (fun stage => ¬ input.contract160.good stage)))

def preserveFrom158 (input : Inputs previous) {Result : input.S158 → Sort v}
    (query : Core.Residual.Query input.S158 Result) :=
  input.preserveFrom159 (query.preserve (Added := fun stage =>
    ∃ candidate, input.contract159.admissible stage candidate))

def preserveFrom157 (input : Inputs previous) {Result : input.S157 → Sort v}
    (query : Core.Residual.Query input.S157 Result) :=
  input.preserveFrom158
    (query.preserve (Added := fun stage => input.contract158.bounded stage))

def preserveFrom156 (input : Inputs previous) {Result : input.S156 → Sort v}
    (query : Core.Residual.Query input.S156 Result) :=
  input.preserveFrom157 (query.preserve (Added := input.Germ))

def preserveFrom155 (input : Inputs previous) {Result : input.S155 → Sort v}
    (query : Core.Residual.Query input.S155 Result) :=
  input.preserveFrom156 (query.preserve (Added :=
    Core.Residual.Decision.Binary input.contract156.event
      (fun stage => ¬ input.contract156.event stage)))

def preserveFrom154 (input : Inputs previous) {Result : input.S154 → Sort v}
    (query : Core.Residual.Query input.S154 Result) :=
  input.preserveFrom155 (query.preserve (Added := input.Certificate))

def preserveFrom153 (input : Inputs previous) {Result : input.S153 → Sort v}
    (query : Core.Residual.Query input.S153 Result) :=
  input.preserveFrom154 (query.preserve (Added :=
    Core.Residual.Decision.Binary
      (Hit154 input.contract154) (NoHit154 input.contract154)))

def preserveFrom152 (input : Inputs previous) {Result : input.S152 → Sort v}
    (query : Core.Residual.Query input.S152 Result) :=
  input.preserveFrom153 (query.preserve (Added := input.Scan))

def preserveFrom151 (input : Inputs previous) {Result : input.S151 → Sort v}
    (query : Core.Residual.Query input.S151 Result) :=
  input.preserveFrom152 (query.preserve (Added := input.Stubs))

def preserveFrom150 (input : Inputs previous) {Result : input.S150 → Sort v}
    (query : Core.Residual.Query input.S150 Result) :=
  input.preserveFrom151 (query.preserve (Added := input.Filter))

def preserveFrom149 (input : Inputs previous) {Result : input.S149 → Sort v}
    (query : Core.Residual.Query input.S149 Result) :=
  input.preserveFrom150 (query.preserve (Added := input.Cold))

def preserveFrom148 (input : Inputs previous) {Result : input.S148 → Sort v}
    (query : Core.Residual.Query input.S148 Result) :=
  input.preserveFrom149 (query.preserve (Added := input.Audit))

def preserveFrom147 (input : Inputs previous) {Result : input.S147 → Sort v}
    (query : Core.Residual.Query input.S147 Result) :=
  input.preserveFrom148 (query.preserve (Added := input.Private))

def preserveFrom146 (input : Inputs previous) {Result : input.S146 → Sort v}
    (query : Core.Residual.Query input.S146 Result) :=
  input.preserveFrom147 (query.preserve (Added := input.Route))

def preserveFrom145 (input : Inputs previous) {Result : input.S145 → Sort v}
    (query : Core.Residual.Query input.S145 Result) :=
  input.preserveFrom146 (query.preserve (Added :=
    Core.Residual.Decision.Binary
      (Below146 input.contract146) (AtMost146 input.contract146)))

/-- Preserve any query on the literal cold-branch predecessor through every
ordinary ledger extension performed by this aggregate. -/
noncomputable def preservePrevious
    {Result : Previous → Sort v}
    (input : Inputs previous)
    (query : Core.Residual.Query Previous Result) :=
  let q145 := query.preserve (Added := input.Interface)
  let q146 := q145.preserve (Added :=
    Core.Residual.Decision.Binary
      (Below146 input.contract146) (AtMost146 input.contract146))
  let q147 := q146.preserve (Added := input.Route)
  let q148 := q147.preserve (Added := input.Private)
  let q149 := q148.preserve (Added := input.Audit)
  let q150 := q149.preserve (Added := input.Cold)
  let q151 := q150.preserve (Added := input.Filter)
  let q152 := q151.preserve (Added := input.Stubs)
  let q153 := q152.preserve (Added := input.Scan)
  let q154 := q153.preserve (Added :=
    Core.Residual.Decision.Binary
      (Hit154 input.contract154) (NoHit154 input.contract154))
  let q155 := q154.preserve (Added := input.Certificate)
  let q156 := q155.preserve (Added :=
    Core.Residual.Decision.Binary input.contract156.event
      (fun stage => ¬ input.contract156.event stage))
  let q157 := q156.preserve (Added := input.Germ)
  let q158 := q157.preserve (Added :=
    fun stage => input.contract158.bounded stage)
  let q159 := q158.preserve (Added :=
    fun stage => ∃ candidate,
      input.contract159.admissible stage candidate)
  let q160 := q159.preserve (Added :=
    Core.Residual.Decision.Binary input.contract160.good
      (fun stage => ¬ input.contract160.good stage))
  let q161 := q160.preserve (Added := input.Evidence)
  let q162 := q161.preserve (Added := input.Residual)
  let q163 := q162.preserve (Added := input.contract163.package)
  q163.preserve (Added := input.Package)

/-- Public final-residual queries for every fact introduced by nodes
145--164. -/
def interfaceAt164Query (input : Inputs previous) :=
  input.preserveFrom145 (interfaceQuery (Interface := input.Interface))

def decision146At164Query (input : Inputs previous) :=
  input.preserveFrom146 (decision146Query (contract := input.contract146))

def routeAt164Query (input : Inputs previous) :=
  input.preserveFrom147 (routeQuery (Route := input.Route))

def privateAt164Query (input : Inputs previous) :=
  input.preserveFrom148 (privateQuery (Private := input.Private))

def auditAt164Query (input : Inputs previous) :=
  input.preserveFrom149 (auditQuery (Audit := input.Audit))

def coldAt164Query (input : Inputs previous) :=
  input.preserveFrom150 (coldQuery (Cold := input.Cold))

def filterAt164Query (input : Inputs previous) :=
  input.preserveFrom151 (filterQuery (Filter := input.Filter))

def stubsAt164Query (input : Inputs previous) :=
  input.preserveFrom152 (stubsQuery (Stubs := input.Stubs))

def scanAt164Query (input : Inputs previous) :=
  input.preserveFrom153 (scanQuery (Scan := input.Scan))

def decision154At164Query (input : Inputs previous) :=
  input.preserveFrom154 (decision154Query (contract := input.contract154))

def certificateAt164Query (input : Inputs previous) :=
  input.preserveFrom155
    (certificateQuery (Certificate := input.Certificate))

def decision156At164Query (input : Inputs previous) :=
  input.preserveFrom156 (decision156Query (contract := input.contract156))

def germAt164Query (input : Inputs previous) :=
  input.preserveFrom157 (germQuery (Germ := input.Germ))

def bounded158At164Query (input : Inputs previous) :=
  input.preserveFrom158 (bounded158Query (contract := input.contract158))

def witness159At164Query (input : Inputs previous) :=
  input.preserveFrom159 (witness159Query (contract := input.contract159))

def decision160At164Query (input : Inputs previous) :=
  input.preserveFrom160 (decision160Query (contract := input.contract160))

def evidenceAt164Query (input : Inputs previous) :=
  input.preserveFrom161 (evidenceQuery (Evidence := input.Evidence))

def residual162At164Query (input : Inputs previous) :=
  input.preserveFrom162 (residual162Query (Residual := input.Residual))

def package163At164Query (input : Inputs previous) :=
  input.preserveFrom163 (package163Query (contract := input.contract163))

def package164At164Query (input : Inputs previous) :=
  package164Query (Package := input.Package)

end Inputs

/-- Registration consists solely of the residual query supplying the old node
arguments.  It cannot choose a terminal or construct an output. -/
structure Registration (Previous : Type u) where
  inputs : Core.Residual.Query Previous (fun previous => Inputs previous)

/-- The standard executable profile for the registered query. -/
structure Profile (Previous : Type u) where
  registration : Registration Previous

namespace Profile

variable (profile : Profile Previous)

inductive Phase
  | n145 | n146 | n147 | n148 | n149 | n150 | n151 | n152 | n153 | n154
  | n155 | n156 | n157 | n158 | n159 | n160 | n161 | n162 | n163 | n164
  deriving DecidableEq, Fintype

noncomputable def execution : Core.Strategy.CTExecution Previous where
  Terminal := Core.Strategy.CompletedTerminal
  Output := fun previous => Stage164
    (Stage163 (profile.registration.inputs previous).contract163)
    (profile.registration.inputs previous).Package
  run := fun previous => (profile.registration.inputs previous).stage164
  terminal := fun _ _ => .completed
  checks := fun _ => Fintype.card Phase
  work := fun _ => Fintype.card Phase

/-- The literal predecessor consumed by this residual-producing strategy. -/
def inputResidualQuery :
    Core.Residual.Query Previous (fun _ => Previous) :=
  id

/- The exact node-164-shaped residual returned by the execution. -/
noncomputable def outputResidual (profile : Profile Previous)
    (previous : Previous) : profile.execution.Output previous :=
  profile.execution.run previous

/-- The final node-164-equivalent residual query. -/
def residualQuery :
    Core.Residual.Query (profile.execution.Output previous)
      (fun _ => profile.execution.Output previous) :=
  id

end Profile

/-! ## Framework-registered overflow continuation

The public boundary consumes and retains the literal active overflow stage.
It manufactures no successor payload; graph-owned cold producers are the
only declarations permitted to extend this stage.
-/

structure LedgerProfile (Previous : Type u) (Residual : Type uResidual)
    [Core.Residual.HasResidual Previous Residual]
    (Target : Residual → Prop)
    (packingSemantics :
      Core.Strategy.ObstructionPackingClosure.Semantics.{uResidual, uPacking}
        Residual Target) where
  Owner : Previous → Type uOwner
  family : Core.Residual.Query Previous fun previous =>
    Core.Finite.ColdCorridor.Producer.FamilyProducer.{
      uOwner, uItem, uState, uOutput} (Owner previous)
  current : Core.Residual.Query Previous fun _ => Residual :=
    Core.Residual.Query.residual
  packing : Core.Residual.Query Previous fun previous =>
    Core.Strategy.ObstructionPackingClosure.Packing
      (packingSemantics.occurrences (current previous))
      (packingSemantics.conflict (current previous))
  packing_nonempty : Core.Residual.Query Previous fun previous =>
    (packing previous).selected ≠ []
  barrierSummary : Core.Residual.Query Previous fun _ =>
    Core.Strategy.FiniteBarrierEnumeration.Summary
  overflow : OverflowLedger Previous
  Closure : Previous → Type uClosure
  closure : Core.Residual.Query Previous Closure
  /-- Follows `ObstructionPackingClosure.Semantics.freeForcesTarget` at
  `Core/Strategy/ObstructionPackingSemantics.lean:28`.  The registering
  layer's inert mathematical presentation of the stored (F1) first failure: a
  total implication from a ledger read -- an owner of the (F1) partition
  **stored** in the classified cold entry -- to the registered target.  Core
  never inspects it; it only decides, by reading that same stored partition,
  whether the hypothesis is inhabited. -/
  storedF1ForcesTarget : (previous : Previous) →
    (stage : (family previous).ClassifiedStateStage Previous) →
    (family previous).FailureOwner
        ((family previous).storedClassificationQuery stage) .f1 →
      Target (current previous)
  /-- The germ trichotomy on a branch whose stored (F1) partition is empty.
  Core reads that partition first and only then consults this field. -/
  classifiedStateForcesTarget : (previous : Previous) →
    (stage : (family previous).ClassifiedStateStage Previous) →
      Option (PLift (Target (current previous)))

inductive Terminal
  | familyScan
  | targetClosed
  deriving DecidableEq, Repr

namespace LedgerProfile

variable {Previous : Type u} {Residual : Type uResidual}
variable [Core.Residual.HasResidual Previous Residual]
variable {Target : Residual → Prop}
variable {packingSemantics :
  Core.Strategy.ObstructionPackingClosure.Semantics.{uResidual, uPacking}
    Residual Target}
variable (profile : LedgerProfile.{u, uResidual, uPacking, uClosure,
  uOwner, uItem, uState, uOutput}
  Previous Residual Target packingSemantics)

/-- The graph/domain family is read from the literal active predecessor.
Its owner type and producer remain indexed by that stage, so no residual-level
callback can reconstruct the packing, handoff schedule, or route payload. -/
noncomputable def familyQuery :
    Core.Residual.Query Previous (fun previous =>
      Core.Finite.ColdCorridor.Producer.FamilyProducer
        (profile.Owner previous)) :=
  profile.family

noncomputable def familyAt (previous : Previous) :=
  profile.familyQuery previous

/-- The newest ledger entry stores the exact finite corridor classification
and its dependent F5-owner schedule together. -/
abbrev CorridorStateStage (previous : Previous) :=
  (profile.familyAt previous).ClassifiedStateStage Previous

/-- Consumes `FamilyProducer.classifyStateIntoLedger` at
`Core/Finite/ColdCorridor.lean:1641`.  The literal classified cold ledger
entry appended by the family scan; it was already the `run` of this
execution. -/
noncomputable def classifiedStage (previous : Previous) :
    profile.CorridorStateStage previous :=
  (profile.familyAt previous).classifyStateIntoLedger previous

/-- Follows `ObstructionPackingClosure.Profile.OutcomeAt` at
`Core/Strategy/ObstructionPackingClosure.lean:250`.  The left branch is the
retained classified cold ledger entry; the right branch is the registered
target.  The target therefore lives in the payload type, so the compiler's
`certify` is a projection. -/
abbrev Outcome (previous : Previous) :=
  Sum (profile.CorridorStateStage previous)
    (PLift (Target (profile.current previous)))

/-- Follows `ObstructionPackingClosure.Profile.outcomeAt` at
`Core/Strategy/ObstructionPackingClosure.lean:258`, and consumes
`FamilyProducer.storedF1OwnersQuery` at `Core/Finite/ColdCorridor.lean`.
Run the family scan, then read the stored (F1) partition of the entry it just
wrote.  A nonempty stored partition is exactly the registered forcing
implication's hypothesis, so the outcome is the target; otherwise the
classified entry is retained unchanged. -/
noncomputable def outcome (previous : Previous) : profile.Outcome previous :=
  match ((profile.familyAt previous).storedF1OwnersQuery
      (profile.classifiedStage previous)).values with
  | owner :: _ =>
      Sum.inr (PLift.up (profile.storedF1ForcesTarget previous
        (profile.classifiedStage previous) owner))
  | [] =>
    match profile.classifiedStateForcesTarget previous
        (profile.classifiedStage previous) with
    | none => Sum.inl (profile.classifiedStage previous)
    | some target => Sum.inr target

noncomputable def execution : Core.Strategy.CTExecution.{u} Previous where
  Terminal := Terminal
  Output := profile.Outcome
  run := profile.outcome
  terminal := fun _previous outcome =>
    match outcome with
    | .inl _ => .familyScan
    | .inr _ => .targetClosed
  checks := fun previous =>
    let family := profile.familyAt previous
    family.owners.values.attach.foldl
      (fun total owner => total + (family.contractAt owner.1).stageMajorSchedule.card)
      0
  work := fun previous =>
    let family := profile.familyAt previous
    family.owners.values.attach.foldl
      (fun total owner => total + (family.contractAt owner.1).stageMajorSchedule.card)
      0

/-- Read the family terminal selected from the classification stored in the
newest ordinary ledger entry.  This query never repeats an event test: it
only inspects the five dependent owner partitions in that entry. -/
noncomputable def terminalQuery {previous : Previous} :
    Core.Residual.Query (profile.execution.Output previous) (fun _ => Terminal) :=
  (profile.execution.terminal previous)

@[simp] theorem terminalQuery_read_run (previous : Previous) :
    profile.terminalQuery (profile.execution.run previous) =
      profile.execution.terminal previous (profile.execution.run previous) :=
  rfl

/-- Preserve an inherited query across the exact family-classification ledger
extension. -/
def preserveIncoming
    {previous : Previous} {Result : Previous → Sort v}
    (query : Core.Residual.Query Previous Result) :
    Core.Residual.Query (profile.CorridorStateStage previous)
      (fun stage => Result stage.previous) :=
  query.preserve (Added := fun _ => (profile.familyAt previous).ClassifiedState)

/-- Preserve the exact packing selected by the predecessor CT. -/
def inheritedPackingQuery {previous : Previous} :
    Core.Residual.Query (profile.CorridorStateStage previous)
      (fun stage =>
        Core.Strategy.ObstructionPackingClosure.Packing
          (packingSemantics.occurrences
            (profile.current stage.previous))
          (packingSemantics.conflict
            (profile.current stage.previous))) :=
  profile.preserveIncoming profile.packing

/-- Preserve the nonemptiness proof attached to that same packing value. -/
def inheritedPackingNonemptyQuery {previous : Previous} :
    Core.Residual.Query (profile.CorridorStateStage previous)
      (fun stage =>
        (profile.inheritedPackingQuery stage).selected ≠ []) := by
  exact profile.preserveIncoming profile.packing_nonempty

/-- Cardinality is a view of the preserved packing, never an independently
registered scalar. -/
def inheritedPackingCountQuery {previous : Previous} :
    Core.Residual.Query (profile.CorridorStateStage previous) (fun _ => Nat) :=
  profile.inheritedPackingQuery.map fun _ packing => packing.selected.length

/-- Positivity is derived from the nonemptiness proof attached to the same
preserved packing value. -/
def inheritedPackingCountPositiveQuery {previous : Previous} :
    Core.Residual.Query (profile.CorridorStateStage previous)
      (fun stage => 0 < profile.inheritedPackingCountQuery stage) :=
  profile.inheritedPackingNonemptyQuery.dependentMap fun _ nonempty =>
    List.length_pos_iff.mpr nonempty

/-- Preserve the exact finite-barrier summary written by the predecessor
strategy.  The cold continuation reads this query from the active ledger; it
does not recompute the node-[21] rows or their aggregate products. -/
def inheritedBarrierSummaryQuery {previous : Previous} :
    Core.Residual.Query (profile.CorridorStateStage previous)
      (fun _ => Core.Strategy.FiniteBarrierEnumeration.Summary) :=
  profile.preserveIncoming profile.barrierSummary

/-- Preserve the complete predecessor-owned density-overflow ledger.  Its
three queries continue to point at the literal incoming stage. -/
def inheritedOverflowLedger {previous : Previous} :
    OverflowLedger (profile.CorridorStateStage previous) :=
  profile.overflow.preserve

/-- Read the inherited minimal-context closure capability through the same
ledger extension.  Its index remains the actual predecessor stage. -/
def inheritedClosureQuery {previous : Previous} :
    Core.Residual.Query (profile.CorridorStateStage previous)
      (fun stage => profile.Closure stage.previous) :=
  profile.preserveIncoming profile.closure

@[simp] theorem execution_run_incoming (previous : Previous) :
    (profile.classifiedStage previous).previous = previous := rfl

@[simp] theorem inheritedPackingQuery_read_run (previous : Previous) :
    profile.inheritedPackingQuery (profile.classifiedStage previous) =
      profile.packing previous := rfl

@[simp] theorem inheritedPackingNonemptyQuery_read_run (previous : Previous) :
    profile.inheritedPackingNonemptyQuery (profile.classifiedStage previous) =
      profile.packing_nonempty previous := rfl

@[simp] theorem inheritedPackingCountQuery_read_run (previous : Previous) :
    profile.inheritedPackingCountQuery (profile.classifiedStage previous) =
      (profile.packing previous).selected.length := rfl

@[simp] theorem inheritedBarrierSummaryQuery_read_run (previous : Previous) :
    profile.inheritedBarrierSummaryQuery (profile.classifiedStage previous) =
      profile.barrierSummary previous := rfl

@[simp] theorem inheritedOverflowLowerMass_read_run (previous : Previous) :
    profile.inheritedOverflowLedger.lowerMass
        (profile.classifiedStage previous) =
      profile.overflow.lowerMass previous := rfl

@[simp] theorem inheritedOverflowCapacity_read_run (previous : Previous) :
    profile.inheritedOverflowLedger.capacity
        (profile.classifiedStage previous) =
      profile.overflow.capacity previous := rfl

@[simp] theorem inheritedClosureQuery_read_run (previous : Previous) :
    profile.inheritedClosureQuery (profile.classifiedStage previous) =
      profile.closure previous := rfl

/-- Read the complete Core-produced corridor-family classification from the
newest ledger entry. -/
noncomputable def familyClassificationQuery {previous : Previous} :
    Core.Residual.Query (profile.CorridorStateStage previous)
      (fun _ => (profile.familyAt previous).Classification) :=
  (profile.familyAt previous).storedClassificationQuery

/-- Read Core's exact first non-F5 search from the same cold ledger entry as
the family classification.  This is the standard ordered-exhaustion handle
used to route an F1--F4 hit or retain the all-F5 alternative. -/
noncomputable def firstNonF5Query {previous : Previous} :
    Core.Residual.Query (profile.CorridorStateStage previous)
      (fun stage => Core.Finite.Search.Execution
        (profile.familyAt previous).owners.attach
        (fun owner => ¬ Core.Finite.ColdCorridor.Contract.Classification.IsFailure
          ((profile.familyAt previous).contractAt owner.1)
          ((profile.familyClassificationQuery stage).classify owner) .f5)) :=
  (profile.familyAt previous).storedFirstNonF5Query

/-- In the no-hit branch of the stored ordered exhaustion, every exact owner
is selected by the F5 partition of that same ledger entry. -/
theorem allOwnersF5OfNoFirstNonF5 {previous : Previous}
    (stage : profile.CorridorStateStage previous)
    (absent : ¬ (profile.firstNonF5Query stage).HasHit)
    (owner : {owner : profile.Owner previous //
      owner ∈ (profile.familyAt previous).owners.values}) :
    Core.Finite.ColdCorridor.Contract.Classification.IsFailure
      ((profile.familyAt previous).contractAt owner.1)
      ((profile.familyClassificationQuery stage).classify owner) .f5 :=
  (profile.familyAt previous).storedAllOwnersF5OfNoFirstNonF5
    stage absent owner

/-- In the hit branch of the stored ordered exhaustion, recover the exact
scheduled owner together with its exhaustive F1--F4 classification. -/
theorem firstNonF5Partition {previous : Previous}
    (stage : profile.CorridorStateStage previous)
    (found : (profile.firstNonF5Query stage).HasHit) :
    let owner := (profile.firstNonF5Query stage).hitOfHasHit found |>.value
    let family := profile.familyAt previous
    let classification := profile.familyClassificationQuery stage
    Core.Finite.ColdCorridor.Contract.Classification.IsFailure
        (family.contractAt owner.1) (classification.classify owner) .f1 ∨
      Core.Finite.ColdCorridor.Contract.Classification.IsFailure
        (family.contractAt owner.1) (classification.classify owner) .f2 ∨
      Core.Finite.ColdCorridor.Contract.Classification.IsFailure
        (family.contractAt owner.1) (classification.classify owner) .f3 ∨
      Core.Finite.ColdCorridor.Contract.Classification.IsFailure
        (family.contractAt owner.1) (classification.classify owner) .f4 := by
  dsimp only
  exact (profile.familyAt previous).storedFirstNonF5Partition stage found

/-- Framework focus for the stored first-non-F5 hit branch.  The refinement
reads only the `hit?` tag of Core's retained ordered-exhaustion value; it does
not execute the family classifier or its search again. -/
noncomputable def firstNonF5HitFocus {previous : Previous} :
    Core.Residual.Focus.Profile (profile.CorridorStateStage previous) :=
  let parent := Core.Residual.Focus.always (profile.CorridorStateStage previous)
  let stored := Core.Residual.Focus.ActiveQuery.ofQuery
    (profile := parent) profile.firstNonF5Query
  Core.Residual.Focus.refine parent
    (Core.Residual.Focus.ActiveQuery.tagEqualTo stored
      (fun _stage _active execution => execution.hit?.isSome) true)

/-- Complementary framework focus for the exact all-F5 branch.  Like the hit
focus, it inspects only the stored search tag and retains the entire incoming
classification ledger unchanged. -/
noncomputable def allF5Focus {previous : Previous} :
    Core.Residual.Focus.Profile (profile.CorridorStateStage previous) :=
  let parent := Core.Residual.Focus.always (profile.CorridorStateStage previous)
  let stored := Core.Residual.Focus.ActiveQuery.ofQuery
    (profile := parent) profile.firstNonF5Query
  Core.Residual.Focus.refine parent
    (Core.Residual.Focus.ActiveQuery.tagEqualTo stored
      (fun _stage _active execution => execution.hit?.isSome) false)

/-- A focused hit view carries the exact `HasHit` proof for the retained
search. -/
theorem firstNonF5HasHitOfActive {previous : Previous}
    (view : Core.Residual.Focus.ActiveView
      (profile.firstNonF5HitFocus (previous := previous))) :
    (profile.firstNonF5Query view.previous).HasHit := by
  rcases view.proof with ⟨_trivial, selected⟩
  change (profile.firstNonF5Query view.previous).hit?.isSome = true at selected
  simpa [Core.Finite.Search.Execution.HasHit] using selected

/-- An all-F5 focused view carries the exact no-hit proof for the retained
search. -/
theorem noFirstNonF5OfAllF5Active {previous : Previous}
    (view : Core.Residual.Focus.ActiveView
      (profile.allF5Focus (previous := previous))) :
    ¬ (profile.firstNonF5Query view.previous).HasHit := by
  rcases view.proof with ⟨_trivial, selected⟩
  change (profile.firstNonF5Query view.previous).hit?.isSome = false at selected
  simpa [Core.Finite.Search.Execution.HasHit] using selected

/-- Read the exact F1-owner schedule from the newest stored partition. -/
noncomputable def f1OwnersQuery {previous : Previous} :
    Core.Residual.Query (profile.CorridorStateStage previous)
      (fun stage => Core.Finite.Enumeration
        ((profile.familyAt previous).FailureOwner
          (profile.familyClassificationQuery stage) .f1)) :=
  (profile.familyAt previous).storedF1OwnersQuery

/-- Read the exact F2-owner schedule from the newest stored partition. -/
noncomputable def f2OwnersQuery {previous : Previous} :
    Core.Residual.Query (profile.CorridorStateStage previous)
      (fun stage => Core.Finite.Enumeration
        ((profile.familyAt previous).FailureOwner
          (profile.familyClassificationQuery stage) .f2)) :=
  (profile.familyAt previous).storedF2OwnersQuery

/-- Read the exact F3-owner schedule from the newest stored partition. -/
noncomputable def f3OwnersQuery {previous : Previous} :
    Core.Residual.Query (profile.CorridorStateStage previous)
      (fun stage => Core.Finite.Enumeration
        ((profile.familyAt previous).FailureOwner
          (profile.familyClassificationQuery stage) .f3)) :=
  (profile.familyAt previous).storedF3OwnersQuery

/-- Read the exact F4-owner schedule from the newest stored partition. -/
noncomputable def f4OwnersQuery {previous : Previous} :
    Core.Residual.Query (profile.CorridorStateStage previous)
      (fun stage => Core.Finite.Enumeration
        ((profile.familyAt previous).FailureOwner
          (profile.familyClassificationQuery stage) .f4)) :=
  (profile.familyAt previous).storedF4OwnersQuery

/-- Read the exact F5-owner schedule from the newest cold ledger entry. -/
noncomputable def survivingOwnersQuery {previous : Previous} :
    Core.Residual.Query (profile.CorridorStateStage previous)
      (fun stage => Core.Finite.Enumeration
        ((profile.familyAt previous).F5Owner
          (profile.familyClassificationQuery stage))) :=
  (profile.familyAt previous).storedSurvivingOwnersQuery

/-- Read the exact repeated-state F5 subschedule from the newest cold ledger
entry.  This is a dependent projection of the stored bounded outcomes; it
does not reconstruct a corridor or rerun the repeated-state search. -/
noncomputable def repeatedSurvivingOwnersQuery {previous : Previous} :
    Core.Residual.Query (profile.CorridorStateStage previous)
      (fun stage => Core.Finite.Enumeration
        ((profile.familyAt previous).RepeatedF5Owner
          ((profile.familyAt previous).classifiedStateQuery stage))) :=
  (profile.familyAt previous).storedRepeatedF5OwnersQuery

/-- Read the exact terminal F5 subschedule from the newest cold ledger entry.
This is the complementary projection of the same stored bounded outcomes used
by `repeatedSurvivingOwnersQuery`; no terminal is selected again. -/
noncomputable def terminalSurvivingOwnersQuery {previous : Previous} :
    Core.Residual.Query (profile.CorridorStateStage previous)
      (fun stage => Core.Finite.Enumeration
        ((profile.familyAt previous).TerminalF5Owner
          ((profile.familyAt previous).classifiedStateQuery stage))) :=
  (profile.familyAt previous).storedTerminalF5OwnersQuery

/-- Read one scheduled corridor's typed F1--F5 event directly from the
active cold residual.  The owner is indexed by the exact producer schedule,
and the query delegates to Core's existing family-classification ledger. -/
noncomputable def memberClassifiedEventQuery {previous : Previous}
    (owner : {owner : profile.Owner previous //
      owner ∈ (profile.familyAt previous).owners.values}) :
    Core.Residual.Query (profile.CorridorStateStage previous)
      (fun _ => ((profile.familyAt previous).contractAt owner.1).ClassifiedEvent) :=
  (profile.familyAt previous).storedMemberClassifiedEventQuery owner

/-- Exhaustive owner-by-owner partition law read from the same newest family
ledger entry.  Downstream continuations may consume every owner independently;
no global priority terminal is selected and no later partition is dropped. -/
theorem ownerPartition {previous : Previous}
    (stage : profile.CorridorStateStage previous)
    (owner : {owner : profile.Owner previous //
      owner ∈ (profile.familyAt previous).owners.values}) :
    let family := profile.familyAt previous
    let classification := profile.familyClassificationQuery stage
    Core.Finite.ColdCorridor.Contract.Classification.IsFailure
        (family.contractAt owner.1) (classification.classify owner) .f1 ∨
      Core.Finite.ColdCorridor.Contract.Classification.IsFailure
        (family.contractAt owner.1) (classification.classify owner) .f2 ∨
      Core.Finite.ColdCorridor.Contract.Classification.IsFailure
        (family.contractAt owner.1) (classification.classify owner) .f3 ∨
      Core.Finite.ColdCorridor.Contract.Classification.IsFailure
        (family.contractAt owner.1) (classification.classify owner) .f4 ∨
      Core.Finite.ColdCorridor.Contract.Classification.IsFailure
        (family.contractAt owner.1) (classification.classify owner) .f5 := by
  dsimp only
  exact
    Core.Finite.ColdCorridor.Producer.FamilyProducer.ClassifiedState.owner_partition
      (family := profile.familyAt previous)
      ((profile.familyAt previous).classifiedStateQuery stage) owner

/-- Eliminate one owner from an F1--F4 partition into the exact event stored
in the active cold residual.  The dependent owner and its classification are
read from the same newest ledger entry, so this cannot detach a witness from
the residual that produced it. -/
noncomputable def failureEvent {previous : Previous}
    (stage : profile.CorridorStateStage previous)
    (failure : Core.Finite.ColdCorridor.Failure)
    (notF5 : failure ≠ .f5)
    (owner : (profile.familyAt previous).FailureOwner
      (profile.familyClassificationQuery stage) failure) :
    ((profile.familyAt previous).contractAt owner.1.1).EventWitness failure :=
  (profile.familyAt previous).storedFailureEvent stage failure notF5 owner

/-- Recover the universal F5 fact for one surviving owner directly from the
active cold residual. -/
theorem survivingAllF5 {previous : Previous}
    (stage : profile.CorridorStateStage previous)
    (owner : (profile.familyAt previous).F5Owner
      (profile.familyClassificationQuery stage)) :
    ∀ item ∈ ((profile.familyAt previous).contractAt owner.1.1).schedule.values,
      ((profile.familyAt previous).contractAt owner.1.1).f5 item
        (((profile.familyAt previous).contractAt owner.1.1).run item) :=
  (profile.familyAt previous).storedAllF5 stage owner

/-- Recover Core's bounded-trace alternative for the same F5 owner from the
same newest ledger entry. -/
noncomputable def survivingBoundedOutcome {previous : Previous}
    (stage : profile.CorridorStateStage previous)
    (owner : (profile.familyAt previous).F5Owner
      (profile.familyClassificationQuery stage)) :
    @Core.Finite.ColdCorridor.Contract.StateTrace.BoundedOutcome
      ((profile.familyAt previous).Item owner.1.1)
      ((profile.familyAt previous).State owner.1.1)
      ((profile.familyAt previous).stateFintype owner.1.1)
      ((profile.familyAt previous).traceAt owner.1.1) :=
  (profile.familyAt previous).storedF5BoundedOutcome stage owner

/-- Recover the repeated-state witness for an owner selected by the exact
repeated-F5 query on this active residual. -/
noncomputable def repeatedSurvivingWitness {previous : Previous}
    (stage : profile.CorridorStateStage previous)
    (owner : (profile.familyAt previous).RepeatedF5Owner
      ((profile.familyAt previous).classifiedStateQuery stage)) :
    @Core.Finite.ColdCorridor.Contract.StateTrace.BoundedRepeat
      ((profile.familyAt previous).Item owner.1.1.1)
      ((profile.familyAt previous).State owner.1.1.1)
      ((profile.familyAt previous).stateFintype owner.1.1.1)
      ((profile.familyAt previous).traceAt owner.1.1.1) :=
  (profile.familyAt previous).storedRepeatedF5Witness stage owner

/-- Recover the exact finite-state bound for an owner selected by the terminal
F5 query on this active residual. -/
def terminalSurvivingBound {previous : Previous}
    (stage : profile.CorridorStateStage previous)
    (owner : (profile.familyAt previous).TerminalF5Owner
      ((profile.familyAt previous).classifiedStateQuery stage)) :
    (@Core.Finite.ColdCorridor.Contract.StateTrace.schedule
      ((profile.familyAt previous).Item owner.1.1.1)
      ((profile.familyAt previous).State owner.1.1.1)
      ((profile.familyAt previous).stateFintype owner.1.1.1)
      ((profile.familyAt previous).traceAt owner.1.1.1)).card ≤
      @Fintype.card ((profile.familyAt previous).State owner.1.1.1)
        ((profile.familyAt previous).stateFintype owner.1.1.1) :=
  (profile.familyAt previous).storedTerminalF5Bound stage owner

end LedgerProfile

end Hypostructure.Core.Strategy.ColdBranchAggregation
