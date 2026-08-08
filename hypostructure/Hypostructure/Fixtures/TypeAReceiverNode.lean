import Hypostructure.Graph.Strategy.SpineContinuationRun

/-!
# Fixture: nodes `[88]` and `[89]`, the Type A receiver split

The two rows of the Type A entry — the canonical receiver routing with its
threshold algebra, and the saturation question asked on it — are quantified
over the keys they commit.  This fixture installs them at the spine's *own*
vocabulary, on the ledger node `[63]`'s Type A arm leaves, and checks the four
things the audit's Ledger, Transport, Residual and Facts columns claim:

* node `[88]` elaborates only as an `AtomicStrategy` run against the literal
  incoming branch cursor, and its output index is definitionally the incoming
  one with the routing key appended: nothing is archived to make room;
* node `[89]` elaborates only as a `Decision` against the routing cursor, so it
  cannot be asked on a history that has not reached the Type A residual and
  committed the routing;
* the arm not taken is absent from the taken branch's key index, so a
  downstream row cannot read the alternative its branch did not commit;
* the audit of each exit lists exactly the facts that branch committed, in
  commit order, with no duplicate.

It also exercises the two statements node `[88]` rests on directly at the
framework level: the routing is total under the empty-core hypothesis, and
unsaturation is exactly nonnegative final charge.

Nothing here is specific to one manuscript: the rows run at the framework's own
`Spine.Data`, left as a parameter, and the graph-level checks quantify over an
arbitrary object, support, baseline and scale.
-/

namespace Hypostructure.Fixtures.TypeAReceiverNode

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[88]`: the routing, run on the Type A cursor -/

/-- **The routing row runs against the literal Type A residual.**

The requirement `remainderNormalized` is discharged by instance resolution
against the incoming index, and the freshness side condition is decided on the
vocabulary's own finite `Key`.  The output index is
`typeAReceiverRoutingKeys`, which is `typeALowSurplusKeys` with one entry
appended — the row reconstructs no cursor and re-reads no root. -/
noncomputable def receiverRouting
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeALowSurplusKeys) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      typeAReceiverRoutingKeys :=
  (typeAReceiverRouting (data := data)).run history (by simp)

/-- **The row's declared output is exactly the routing key.**  A row that
committed a second fact, or none, would not have this manifest. -/
example :
    (typeAReceiverRouting (BranchState := BranchState)
        (presentation := presentation) (data := data)).manifest.Produces =
      [K .typeAReceiverRouting] :=
  rfl

/-- **Every earlier fact survives.**  The Type A residual's own fact is still
indexed after the routing is committed, which is what lets node `[89]` read the
support it is asking about. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeALowSurplus) ∈
      typeAReceiverRoutingKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

/-! ## Node `[89]`: the saturation question, asked on the routing cursor -/

/-- **The saturation question, asked on the cursor node `[88]` left.** -/
noncomputable def saturation
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeAReceiverRoutingKeys) :
    Decision (K .typeASaturatedReceiver) (K .typeAUnsaturatedReceivers)
      history :=
  typeASaturationDichotomy history (K .typeALowSurplus)
    (K .typeASaturatedReceiver) (K .typeAUnsaturatedReceivers)
    (fun fact => fact.down) (fun saturated => ⟨saturated⟩)
    (fun unsaturated => ⟨unsaturated⟩) (by simp) (by simp)

/-! ## What the two exits carry -/

theorem saturatedReceiver_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeASaturatedReceiverKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem unsaturatedReceivers_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeAUnsaturatedReceiverKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem saturatedReceiver_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeASaturatedReceiverKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem unsaturatedReceivers_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeAUnsaturatedReceiverKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

/-- **The two arms of node `[89]` are distinct branches.**  Neither index
contains the other's key, which is the type-level statement that node `[93]`
cannot read the unsaturated capacity and node `[90]` cannot read the saturated
receiver. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAUnsaturatedReceivers) ∉
      typeASaturatedReceiverKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeASaturatedReceiver) ∉
      typeAUnsaturatedReceiverKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

/-- **Both arms carry the routing.**  `L(w)` is a complete assignment on either
arm, which is what node `[90]`'s discharging and node `[93]`'s port analysis
each need. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAReceiverRouting) ∈
      typeASaturatedReceiverKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAReceiverRouting) ∈
      typeAUnsaturatedReceiverKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

/-- **The Type B alternative of node `[62]` is on neither arm.**  The Type A
ladder cannot read the fact the sibling branch committed. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeBHighSurplus) ∉
      typeAUnsaturatedReceiverKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

/-! ## The graph statements the rows rest on

Both are checked at an arbitrary object, support, baseline and scale: neither
knows a degree, an overload factor, or a graph family. -/

/-- **The routing is total under the empty-core hypothesis.**  A vertex
spending the whole baseline is routed, and to a receiver —
`lem:typeA-receiver-loads` in the form the row commits it.  No cappedness is
needed: the reachable region is the vertices at *or above* the baseline, so the
only alternative to a trace is a subregion meeting the baseline, which node
`[27]` denies. -/
example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat)
    (noCore : ∀ inner : Finset object.Vertex, inner ⊆ support →
      ¬ Graph.MinimumDegreeAtLeast threshold (object.induce inner))
    {source : object.Vertex} (member : source ∈ support)
    (full : object.internalDegree support source = threshold) :
    ∃ receiver : object.Vertex,
      object.traceReceiver? support threshold source = some receiver ∧
        object.IsReceiver support threshold receiver := by
  obtain ⟨target, trace⟩ :=
    object.exists_traceTo_of_no_baseline_subsupport support threshold
      noCore member (le_of_eq full.symm)
  obtain ⟨found, routed⟩ :=
    Option.isSome_iff_exists.mp (object.isSome_traceReceiver?_of_traceTo trace)
  exact ⟨found, routed,
    object.isReceiver_of_traceTo (object.traceTo_of_traceReceiver?_eq_some routed)⟩

/-- **A routed vertex has a canonical trace, to the receiver it was routed
to.**  `r(u)` and `T_u` are one routing: the path selection is asked exactly at
the receiver the vertex selection returned, and the path it produces has the
trace shape. -/
example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat) {source receiver : object.Vertex}
    (routed : object.traceReceiver? support threshold source = some receiver) :
    ∃ trace : object.graph.Path source receiver,
      object.tracePath? support threshold source receiver = some trace ∧
        object.IsTracePath support threshold trace.1 := by
  obtain ⟨trace, selected⟩ :=
    Option.isSome_iff_exists.mp
      (object.isSome_tracePath?_of_traceTo
        (object.traceTo_of_traceReceiver?_eq_some routed))
  exact ⟨trace, selected, object.isTracePath_of_tracePath?_eq_some selected⟩

/-- **Unsaturation is exactly nonnegative final charge**, and the threshold is
the manuscript's `H_j = s·(j+1)`, never above `s·δ` —
`lem:typeA-threshold-algebra` in the form the row commits it. -/
example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold scale : Nat) {receiver : object.Vertex}
    (isReceiver : object.IsReceiver support threshold receiver) :
    (¬ object.Saturated support threshold scale receiver ↔
        1 + object.routedLoad support threshold receiver ≤
          scale * object.missingPorts support threshold receiver) ∧
      scale * object.missingPorts support threshold receiver =
          scale * (threshold - 1 -
            object.internalDegree support receiver + 1) ∧
        scale * object.missingPorts support threshold receiver ≤
          scale * threshold :=
  ⟨object.not_saturated_iff support threshold scale receiver,
    object.saturationThreshold_eq support threshold scale isReceiver.2,
    object.saturationThreshold_le support threshold scale receiver⟩

end Hypostructure.Fixtures.TypeAReceiverNode
