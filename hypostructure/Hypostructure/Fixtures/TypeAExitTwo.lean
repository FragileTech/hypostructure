import Hypostructure.Graph.Strategy.TypeAExitRun

/-!
# Fixture: node `[97]`, exit `(2)` of the saturated exit chain

Exit `(2)` of `def:typeA-saturated-exits` — *"two anchored receiver-entry
returns through one completion port are internally vertex-disjoint as anchored
paths and their lengths sum to a power of two"* — is quantified over the keys it
consumes and commits.  This fixture installs it at the spine's *own* vocabulary,
on the ledger node `[95]`'s free arm leaves, and checks the four things the
audit's Ledger, Transport, Residual and Facts columns claim:

* the question elaborates only as a `Decision` against the literal incoming
  branch cursor, so it cannot be asked on a history that has not walked exit
  `(1)`;
* the arm not taken is absent from the taken branch's key index, so node `[99]`
  cannot read the theta and the closed terminal cannot read the exit-`(2)`-free
  hypothesis;
* the closed arm carries Core's own closure key, appended from node `[97]`'s
  fact and the selection's avoidance rather than asserted by a row;
* the audit of each exit accounts for the whole branch fact index, with no
  duplicate.

It also exercises the three graph statements the row rests on directly at the
framework level: an anchored return through a port has length at least two,
`lem:typeA-common-port-return-cycle` glues two internally disjoint ones into an
accepted cycle, and the exit is stated of the receiver-entry returns
`def:typeA-visible-load` counts.

Nothing here is specific to one manuscript: the row runs at the framework's own
`Spine.Data`, left as a parameter, and the graph-level checks quantify over an
arbitrary object, receiver, port and accepted-length predicate.
-/

namespace Hypostructure.Fixtures.TypeAExitTwo

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[97]`, asked on node `[95]`'s free cursor -/

/-- **Exit `(2)` is asked on the cursor node `[95]` left.**  Its visible-entry
requirement is discharged by instance resolution against the incoming index --
node `[95]` retained node `[93]`'s port -- and both freshness side conditions
are decided on the vocabulary's own finite `Key`. -/
noncomputable def exitTwo
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitOneFreeKeys typeAVisibleEntryKeys)) :
    Decision (K .typeAExitTwoTheta) (K .typeAExitTwoFree) history :=
  typeAExitTwo history (by simp) (by simp)

/-- **The whole node, run: one arm closed, one arm continuing to node `[99]`.** -/
noncomputable def run
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitOneFreeKeys typeAVisibleEntryKeys)) :
    ExitTwoResult selected (typeAExitOneFreeKeys typeAVisibleEntryKeys) :=
  runExitTwo history (by simp) (by simp) (by simp)

/-- **The chain `[95]` → `[97]` → `[99]`, run on node `[93]`'s cursor.**  The
exits are walked in the manuscript's order on one immutable prefix. -/
noncomputable def runChain
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeAVisibleEntryKeys) :
    ExitChainResult selected typeAVisibleEntryKeys :=
  runExitChain history (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp)

/-! ## What the two exits carry -/

/-- **The two arms of node `[97]` are distinct branches.**  Neither index
contains the other's key. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAExitTwoFree) ∉
      typeAExitTwoClosedKeys (BranchState := BranchState)
        (presentation := presentation)
        (typeAExitOneFreeKeys (data := data) typeAVisibleEntryKeys) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAExitTwoTheta) ∉
      typeAExitTwoFreeKeys (BranchState := BranchState)
        (presentation := presentation)
        (typeAExitOneFreeKeys (data := data) typeAVisibleEntryKeys) := by
  simp

/-- **The closed arm carries the closure key**, and the arm that continues to
node `[99]` does not: exit `(2)`'s no arm is an open residual, exactly as
`lem:typeA-exits-discharged` leaves it. -/
example :
    (closed (BranchState := BranchState) (presentation := presentation)
        (data := data)) ∈
      typeAExitTwoClosedKeys (BranchState := BranchState)
        (presentation := presentation)
        (typeAExitOneFreeKeys (data := data) typeAVisibleEntryKeys) := by
  simp

example :
    (closed (BranchState := BranchState) (presentation := presentation)
        (data := data)) ∉
      typeAExitTwoFreeKeys (BranchState := BranchState)
        (presentation := presentation)
        (typeAExitOneFreeKeys (data := data) typeAVisibleEntryKeys) := by
  simp

/-- **Both arms still carry node `[93]`'s port and node `[95]`'s hypothesis.**
The exit list is a walk on one prefix: exit `(3)` is asked at node `[99]` under
both of the alternatives already denied. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAVisibleEntry) ∈
      typeAExitTwoFreeKeys (BranchState := BranchState)
        (presentation := presentation)
        (typeAExitOneFreeKeys (data := data) typeAVisibleEntryKeys) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAExitOneFree) ∈
      typeAExitTwoFreeKeys (BranchState := BranchState)
        (presentation := presentation)
        (typeAExitOneFreeKeys (data := data) typeAVisibleEntryKeys) := by
  simp

/-- **Node `[95]`'s sibling arm is on neither arm of node `[97]`.**  The theta
question cannot read the Mersenne return. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAExitOneReturn) ∉
      typeAExitTwoFreeKeys (BranchState := BranchState)
        (presentation := presentation)
        (typeAExitOneFreeKeys (data := data) typeAVisibleEntryKeys) := by
  simp

/-! ## The graph statements the row rests on

All three are checked at an arbitrary object, receiver, port and accepted-length
predicate: none knows a degree, an overload factor, or a graph family. -/

/-- **An anchored return through a port has length at least two.**  This is the
nondegeneracy `lem:two-path-criterion` asks for, and it comes from the port
alone: its two ends are adjacent, and the return avoids the port edge. -/
example (object : Graph.FiniteObject.{u}) {receiver outside : object.Vertex}
    (adjacent : object.graph.Adj receiver outside)
    (return' : Graph.VisibleEntry.AnchoredReturn object receiver outside) :
    2 ≤ return'.path.length :=
  Graph.VisibleEntry.AnchoredReturn.two_le_length adjacent return'

/-- **`lem:typeA-common-port-return-cycle`.**  Two internally vertex-disjoint
anchored returns through one completion port glue into a simple cycle of length
`|P₁| + |P₂|`; if that sum is accepted, the object carries an accepted cycle. -/
example (object : Graph.FiniteObject.{u}) (CycleLengthOK : Nat → Prop)
    {receiver outside : object.Vertex}
    (adjacent : object.graph.Adj receiver outside)
    (first second : Graph.VisibleEntry.AnchoredReturn object receiver outside)
    (disjoint : Graph.VisibleEntry.InternallyDisjoint first second)
    (accepted : CycleLengthOK (first.path.length + second.path.length)) :
    Graph.HasCycleWithLength CycleLengthOK object :=
  Graph.VisibleEntry.hasCycleWithLength_of_commonPortReturns adjacent first
    second disjoint accepted

/-- **Exit `(2)` exhibits the target.**  This is the whole content of the
closure: the exit and the selection's avoidance are incompatible at the level of
the statements themselves. -/
example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (CycleLengthOK : Nat → Prop) {receiver outside : object.Vertex}
    (avoids : ¬ Graph.HasCycleWithLength CycleLengthOK object)
    (port : outside ∈ Graph.VisibleEntry.completionPorts object support receiver) :
    ¬ Graph.VisibleEntry.ExitTwoThrough object support CycleLengthOK receiver
      outside :=
  fun exit =>
    avoids (Graph.VisibleEntry.hasCycleWithLength_of_exitTwoThrough port exit)

/-- **The exit is asked of receiver-entry returns, not of arbitrary paths.**
Unfolding it produces the pair `def:typeA-visible-load` names, together with the
two side conditions `def:typeA-saturated-exits` (2) states. -/
example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (CycleLengthOK : Nat → Prop) {receiver outside : object.Vertex} :
    Graph.VisibleEntry.ExitTwoThrough object support CycleLengthOK receiver
        outside ↔
      ∃ first second :
          Graph.VisibleEntry.ReceiverEntryReturn object support receiver outside,
        Graph.VisibleEntry.InternallyDisjoint first.toAnchoredReturn
            second.toAnchoredReturn ∧
          CycleLengthOK (first.toAnchoredReturn.path.length +
            second.toAnchoredReturn.path.length) :=
  Iff.rfl

/-! ## The audit of each exit -/

theorem closed_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected
      (typeAExitTwoClosedKeys (typeAExitOneFreeKeys typeAVisibleEntryKeys))) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem free_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected
      (typeAExitTwoFreeKeys (typeAExitOneFreeKeys typeAVisibleEntryKeys))) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem closed_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected
      (typeAExitTwoClosedKeys (typeAExitOneFreeKeys typeAVisibleEntryKeys))) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem free_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected
      (typeAExitTwoFreeKeys (typeAExitOneFreeKeys typeAVisibleEntryKeys))) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem closed_audit_commits_nonempty
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected
      (typeAExitTwoClosedKeys (typeAExitOneFreeKeys typeAVisibleEntryKeys))) :
    (ExactLedger.audit history).commits.Forall fun record =>
      record.produced ≠ [] :=
  ExactLedger.audit_commits_nonempty history

end Hypostructure.Fixtures.TypeAExitTwo
