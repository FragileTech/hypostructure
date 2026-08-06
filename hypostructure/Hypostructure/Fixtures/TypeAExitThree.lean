import Hypostructure.Graph.Strategy.TypeAExitRun

/-!
# Fixture: node `[99]`, exit `(3)` of the saturated exit chain

Exit `(3)` of `def:typeA-saturated-exits` — *"a shared `P₁₃` window violates the
corresponding legal-label relation `C_s`"* — is quantified over the keys it
consumes and commits.  This fixture installs it at the spine's *own* vocabulary,
on the ledger node `[97]`'s free arm leaves, and checks the four things the
audit's Ledger, Transport, Residual and Facts columns claim:

* the question elaborates only as a `Decision` against the literal incoming
  branch cursor, so it cannot be asked on a history that has not walked exits
  `(1)` and `(2)`;
* the arm not taken is absent from the taken branch's key index, so node `[101]`
  cannot read the collision and the closed terminal cannot read the
  exit-`(3)`-free hypothesis;
* the closed arm carries Core's own closure key, appended from node `[99]`'s
  fact and the selection's avoidance rather than asserted by a row;
* the audit of each exit accounts for the whole branch fact index, with no
  duplicate.

It also exercises the graph statements the row rests on directly at the
framework level: the collision clause *is* failure of `lem:labels`' relation
`C_s`, the collision builds an accepted cycle, and the manuscript's own legality
picture — one outside vertex, no connector — is the `s = 0` case of that
construction.

Nothing here is specific to one manuscript: the row runs at the framework's own
`Spine.Data`, left as a parameter, and the graph-level checks quantify over an
arbitrary object, window order, packing and accepted-length predicate.
-/

namespace Hypostructure.Fixtures.TypeAExitThree

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## The cursor node `[97]` leaves -/

/-- The index node `[99]` is asked on: node `[93]`'s port, with exits `(1)` and
`(2)` denied. -/
abbrev entryKeys : FactKeys (Input BranchState Presentation presentation data) :=
  typeAExitTwoFreeKeys (typeAExitOneFreeKeys typeAVisibleEntryKeys)

/-! ## Node `[99]`, asked on node `[97]`'s free cursor -/

/-- **Exit `(3)` is asked on the cursor node `[97]` left.**  Its visible-entry
requirement is discharged by instance resolution against the incoming index --
nodes `[95]` and `[97]` retained node `[93]`'s port — and both freshness side
conditions are decided on the vocabulary's own finite `Key`. -/
noncomputable def exitThree
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected entryKeys) :
    Decision (K .typeAExitThreeCollision) (K .typeAExitThreeFree) history :=
  typeAExitThree history (by simp) (by simp)

/-- **The whole node, run: one arm closed, one arm continuing to node
`[101]`.** -/
noncomputable def run
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected entryKeys) :
    ExitThreeResult selected entryKeys :=
  runExitThree history (by simp) (by simp) (by simp)

/-! ## What the two exits carry -/

/-- **The two arms of node `[99]` are distinct branches.**  Neither index
contains the other's key. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAExitThreeFree) ∉
      typeAExitThreeClosedKeys (BranchState := BranchState)
        (presentation := presentation) (entryKeys (data := data)) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAExitThreeCollision) ∉
      typeAExitThreeFreeKeys (BranchState := BranchState)
        (presentation := presentation) (entryKeys (data := data)) := by
  simp

/-- **The closed arm carries the closure key**, and the arm that continues to
node `[101]` does not: exit `(3)`'s no arm is an open residual, exactly as
`lem:typeA-exits-discharged` leaves it. -/
example :
    (closed (BranchState := BranchState) (presentation := presentation)
        (data := data)) ∈
      typeAExitThreeClosedKeys (BranchState := BranchState)
        (presentation := presentation) (entryKeys (data := data)) := by
  simp

example :
    (closed (BranchState := BranchState) (presentation := presentation)
        (data := data)) ∉
      typeAExitThreeFreeKeys (BranchState := BranchState)
        (presentation := presentation) (entryKeys (data := data)) := by
  simp

/-- **Both arms still carry node `[93]`'s port and the two earlier exits'
hypotheses.**  The exit list is a walk on one prefix: node `[101]` is asked under
all three of the alternatives already denied. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAVisibleEntry) ∈
      typeAExitThreeFreeKeys (BranchState := BranchState)
        (presentation := presentation) (entryKeys (data := data)) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAExitOneFree) ∈
      typeAExitThreeFreeKeys (BranchState := BranchState)
        (presentation := presentation) (entryKeys (data := data)) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAExitTwoFree) ∈
      typeAExitThreeFreeKeys (BranchState := BranchState)
        (presentation := presentation) (entryKeys (data := data)) := by
  simp

/-- **The two earlier exits' sibling arms are on neither arm of node `[99]`.**
The collision question cannot read the Mersenne return or the theta pair. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAExitOneReturn) ∉
      typeAExitThreeFreeKeys (BranchState := BranchState)
        (presentation := presentation) (entryKeys (data := data)) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAExitTwoTheta) ∉
      typeAExitThreeFreeKeys (BranchState := BranchState)
        (presentation := presentation) (entryKeys (data := data)) := by
  simp

/-! ## The graph statements the row rests on

All of them are checked at an arbitrary object, window order, packing and
accepted-length predicate: none knows a degree, a window order, or a forbidden
gap set. -/

/-- **The collision clause is `lem:labels`' own relation, failing.**  At the
registered dyadic target the existential the exit states is exactly
`¬ C_s(S, T)`, so the alternative is the manuscript's and not a surrogate. -/
example {order : Nat} (shift : Nat)
    (source target : Graph.WindowCurvature.Label order) :
    (∃ i ∈ source, ∃ j ∈ target,
        Core.DyadicLength.PowerOfTwoLength
          (Graph.WindowCurvature.closingLength shift (Nat.dist i.1 j.1))) ↔
      ¬ Graph.WindowCurvature.Safe shift source target :=
  Graph.WindowLabelCollision.labelCollision_iff_not_safe

/-- **Exit `(3)` exhibits the target.**  This is the whole content of the
closure: the collision and the selection's avoidance are incompatible at the
level of the statements themselves. -/
example (object : Graph.FiniteObject.{u}) (order : Nat)
    (LengthOK : Nat → Prop) (packing : Finset (Finset object.Vertex))
    (degenerate : ¬ LengthOK 2)
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object) :
    Graph.WindowLabelCollision.LabelCollisionFree object order LengthOK
      packing :=
  fun collision =>
    avoids
      (Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision
        degenerate collision)

/-- **The label is read back as the attachment it records.**  `S(x)` is the
manuscript's `{i : x vᵢ ∈ E(G)}` and nothing else. -/
example (object : Graph.FiniteObject.{u}) {order : Nat}
    (presentation : Graph.TypeBDirectCycle.Presentation object order)
    (outside : object.Vertex) (index : Fin order) :
    index ∈ Graph.WindowLabelCollision.attachmentLabel presentation outside ↔
      object.graph.Adj outside (presentation.coordinate index.1) :=
  Graph.WindowLabelCollision.mem_attachmentLabel

/-- **`lem:labels`' own picture is the `s = 0` case.**  One outside vertex
adjacent to two window coordinates closes a cycle of length `|i − j| + 2`: the
connector is the empty walk, so the collision's closing length is the
manuscript's own. -/
example (object : Graph.FiniteObject.{u}) {order : Nat}
    (LengthOK : Nat → Prop) (packing : Finset (Finset object.Vertex))
    (presentation : Graph.TypeBDirectCycle.Presentation object order)
    (member : presentation.support ∈ packing)
    (outside : object.Vertex)
    (windowFree : ∀ t < order, outside ≠ presentation.coordinate t)
    (first second : Fin order)
    (firstAdj : object.graph.Adj outside (presentation.coordinate first.1))
    (secondAdj : object.graph.Adj outside (presentation.coordinate second.1))
    (accepted : LengthOK (Nat.dist first.1 second.1 + 2)) :
    Graph.WindowLabelCollision.LabelCollision object order LengthOK packing := by
  refine ⟨presentation, member, outside, outside, SimpleGraph.Walk.nil,
    SimpleGraph.Walk.IsPath.nil, ?_, first,
    Graph.WindowLabelCollision.mem_attachmentLabel.mpr firstAdj, second,
    Graph.WindowLabelCollision.mem_attachmentLabel.mpr secondAdj, ?_⟩
  · intro z inside t bound
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at inside
    subst inside
    exact windowFree t bound
  · unfold Graph.WindowCurvature.closingLength
    simp only [SimpleGraph.Walk.length_nil]
    have shifted : (0 : Nat) + 2 + Nat.dist first.1 second.1
        = Nat.dist first.1 second.1 + 2 := by omega
    rw [shifted]
    exact accepted

/-! ## The audit of each exit -/

theorem closed_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitThreeClosedKeys entryKeys)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem free_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitThreeFreeKeys entryKeys)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem closed_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitThreeClosedKeys entryKeys)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem free_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitThreeFreeKeys entryKeys)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem closed_audit_commits_nonempty
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitThreeClosedKeys entryKeys)) :
    (ExactLedger.audit history).commits.Forall fun record =>
      record.produced ≠ [] :=
  ExactLedger.audit_commits_nonempty history

end Hypostructure.Fixtures.TypeAExitThree
