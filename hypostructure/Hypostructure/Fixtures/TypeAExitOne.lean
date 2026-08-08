import Hypostructure.Graph.Strategy.TypeAExitRun

/-!
# Fixture: node `[95]`, exit `(1)` of the saturated exit chain

Exit `(1)` of `def:typeA-saturated-exits` — *"an anchored return through a
completion port of `w` has length in `Mers`"* — is quantified over the keys it
consumes and commits.  This fixture installs it at the spine's *own* vocabulary,
on the ledger node `[93]`'s visible-entry arm leaves, and checks the four things
the audit's Ledger, Transport, Residual and Facts columns claim:

* the question elaborates only as a `Decision` against the literal incoming
  branch cursor, so it cannot be asked on a history that has not entered the
  saturated exit chain;
* the arm not taken is absent from the taken branch's key index, so node `[97]`
  cannot read the Mersenne return and the closed terminal cannot read the
  exit-`(1)`-free hypothesis;
* the closed arm carries Core's own closure key, appended from node `[95]`'s
  fact and the return-avoidance invariant rather than asserted by a row;
* the audit of each exit accounts for the whole branch fact index, with no
  duplicate.

It also exercises the two graph statements the row rests on directly at the
framework level: restoring a completion port over an anchored return of accepted
length realizes the target, and an object whose oriented edges all avoid the
shifted accepted set therefore carries no such return.

Nothing here is specific to one manuscript: the row runs at the framework's own
`Spine.Data`, left as a parameter, and the graph-level checks quantify over an
arbitrary object, port and accepted set.
-/

namespace Hypostructure.Fixtures.TypeAExitOne

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[95]`, asked on node `[93]`'s cursor -/

/-- **Exit `(1)` is asked on the cursor node `[93]` left.**  Its visible-entry
requirement is discharged by instance resolution against the incoming index, and
both freshness side conditions are decided on the vocabulary's own finite
`Key`. -/
noncomputable def exitOne
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeAVisibleEntryKeys) :
    Decision (K .typeAExitOneReturn) (K .typeAExitOneFree) history :=
  typeAExitOne history (by simp) (by simp)

/-! ## What the two exits carry -/

/-- **The two arms of node `[95]` are distinct branches.**  Neither index
contains the other's key. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAExitOneFree) ∉
      typeAExitOneClosedKeys (BranchState := BranchState)
        (presentation := presentation)
        (typeAVisibleEntryKeys (data := data)) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAExitOneReturn) ∉
      typeAExitOneFreeKeys (BranchState := BranchState)
        (presentation := presentation)
        (typeAVisibleEntryKeys (data := data)) := by
  simp

/-- **The closed arm carries the closure key**, and the arm that continues to
node `[97]` does not: exit `(1)`'s no arm is an open residual, exactly as
`lem:typeA-exits-discharged` leaves it. -/
example :
    (closed (BranchState := BranchState) (presentation := presentation)
        (data := data)) ∈
      typeAExitOneClosedKeys (BranchState := BranchState)
        (presentation := presentation)
        (typeAVisibleEntryKeys (data := data)) := by
  simp

example :
    (closed (BranchState := BranchState) (presentation := presentation)
        (data := data)) ∉
      typeAExitOneFreeKeys (BranchState := BranchState)
        (presentation := presentation)
        (typeAVisibleEntryKeys (data := data)) := by
  simp

/-- **Both arms still carry node `[93]`'s visible-entry fact.**  The port exit
`(2)` is asked of at node `[97]` is the one this node was asked of. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAVisibleEntry) ∈
      typeAExitOneFreeKeys (BranchState := BranchState)
        (presentation := presentation)
        (typeAVisibleEntryKeys (data := data)) := by
  simp

/-- **The sibling arm of node `[93]` is on neither arm.**  The exit chain cannot
read `lem:typeA-silent-excess-count`'s quantitative bound. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAVisibleFirstExcess) ∉
      typeAExitOneFreeKeys (BranchState := BranchState)
        (presentation := presentation)
        (typeAVisibleEntryKeys (data := data)) := by
  simp

/-! ## The graph statements the row rests on

Both are checked at an arbitrary object, port and accepted set: neither knows a
degree, an overload factor, or a graph family. -/

/-- **`lem:return-equivalence` at a completion port.**  Restoring the port edge
over an anchored return whose length plus one is accepted realizes the target. -/
example (object : Graph.FiniteObject.{u}) (CycleLengthOK : Nat → Prop)
    {receiver outside : object.Vertex}
    (adjacent : object.graph.Adj receiver outside)
    (return' : Graph.VisibleEntry.AnchoredReturn object receiver outside)
    (accepted : CycleLengthOK (return'.path.length + 1)) :
    Graph.HasCycleWithLength CycleLengthOK object :=
  Graph.VisibleEntry.hasCycleWithLength_of_anchoredReturn CycleLengthOK adjacent
    return' accepted

/-- **The return-avoidance invariant denies exit `(1)`.**  This is the whole
content of the closure: the two facts are incompatible at the level of the
statements themselves. -/
example (object : Graph.FiniteObject.{u}) (CycleLengthOK : Nat → Prop)
    (avoids : ∀ dart : object.graph.Dart,
      Disjoint (Graph.returnLengthSet object dart)
        (Graph.shiftedAcceptedSet CycleLengthOK))
    {receiver outside : object.Vertex}
    (adjacent : object.graph.Adj receiver outside)
    (return' : Graph.VisibleEntry.AnchoredReturn object receiver outside) :
    ¬ CycleLengthOK (return'.path.length + 1) :=
  Graph.VisibleEntry.not_shiftedCycleLength_of_returnLengthSets_disjoint
    CycleLengthOK avoids adjacent return'

/-! ## The audit of each exit -/

theorem closed_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitOneClosedKeys typeAVisibleEntryKeys)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem free_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitOneFreeKeys typeAVisibleEntryKeys)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem closed_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitOneClosedKeys typeAVisibleEntryKeys)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem free_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitOneFreeKeys typeAVisibleEntryKeys)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem closed_audit_commits_nonempty
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitOneClosedKeys typeAVisibleEntryKeys)) :
    (ExactLedger.audit history).commits.Forall fun record =>
      record.produced ≠ [] :=
  ExactLedger.audit_commits_nonempty history

end Hypostructure.Fixtures.TypeAExitOne
