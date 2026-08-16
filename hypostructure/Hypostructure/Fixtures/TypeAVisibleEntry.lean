import Hypostructure.Graph.Strategy.SpineContinuationRun

/-!
# Fixture: node `[93]`, the visible receiver-entry split

Node `[93]` asks whether some completion port of the saturated receiver of a
Type A support carries `s` visible receiver-entry returns.  This fixture
installs the row at the spine's *own* vocabulary, on the cursor node `[89]`'s
saturated arm leaves, and checks the four things the audit's Ledger, Transport,
Residual and Facts columns claim:

* the row elaborates only as a `Decision` against the literal saturated cursor,
  so it cannot be asked on a history that has not reached node `[89]`'s yes arm;
* the arm not taken is absent from the taken branch's key index, so the exit
  chain cannot read node `[94]`'s excess bound and node `[109]` cannot read the
  visible-entry hypothesis;
* both arms retain the whole Type A history, including node `[88]`'s routing,
  which is what makes `L(w)` a complete assignment on either arm;
* the audit of each exit lists exactly the facts that branch committed, in
  commit order, with no duplicate.

It also exercises, at the framework level, the four statements the row rests on
directly: `lem:typeA-first-entry`, both halves of `lem:typeA-entry-budget`, the
per-receiver count of `lem:typeA-silent-excess-count`, and its support-level
form.

Nothing here is specific to one manuscript: the row runs at the framework's own
`Spine.Data`, left as a parameter, and the graph-level checks quantify over an
arbitrary object, support, baseline and scale.
-/

namespace Hypostructure.Fixtures.TypeAVisibleEntry

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## `lem:typeA-port-return`, on the shared prefix

The port test is asked only after the returns are known to exist.  The row
reads the selection by exact key and nothing else, so it elaborates on any
cursor carrying it. -/

/-- **The port non-vacuity, committed on the cursor node `[89]` left.** -/
noncomputable def portReturn
    {selected : Input BranchState Presentation presentation data}
  (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeASaturatedReceiverKeys) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      typeAPortReturnKeys :=
  (typeAPortReturnRow (BranchState := BranchState)
    (presentation := presentation) (data := data)).run history (by
      simp [typeAPortReturnRow, K_eq_iff])

/-! ## Node `[93]`, asked on the port-return cursor -/

/-- **The visible-entry question, asked on the cursor node `[89]` left.**

All three prerequisites -- node `[88]`'s routing, node `[89]`'s saturated
receiver and `lem:typeA-port-return` -- are on the incoming index, the first two
discharged by instance resolution, and the two freshness side conditions are
decided on the vocabulary's own finite `Key`. -/
noncomputable def visibleEntry
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeAPortReturnKeys) :
    Decision (K .typeAVisibleEntry) (K .typeAVisibleFirstExcess) history :=
  typeAVisibleEntryDichotomy history (K .typeAReceiverRouting)
    (K .typeASaturatedReceiver) (K .typeAVisibleEntry)
    (K .typeAVisibleFirstExcess)
    (fun fact packing valid maximal piece inside surplus =>
      fact.down packing valid maximal piece inside surplus)
    (fun fact => fact.down) (fun visible => ⟨visible⟩)
    (fun excess => ⟨excess⟩) (by simp) (by simp)

/-- **Clause (Q1) of `def:typeA-exit4-family`, committed on the yes arm.**  The
canonical family row 16 quantifies over is exhibited at its visible-entry
generator, on the cursor that carries the port. -/
noncomputable def visibleEntryClause
    {selected : Input BranchState Presentation presentation data}
  (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (K .typeAVisibleEntry :: typeAPortReturnKeys)) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      typeAVisibleEntryKeys :=
  (typeAVisibleEntryClauseRow (K .typeAVisibleEntry)
    (K .typeAVisibleEntryClause) (by simp)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)).run history (by simp)

/-! ## What the two exits carry -/

theorem visibleEntry_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeAVisibleEntryKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem visibleFirstExcess_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeAVisibleFirstExcessKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem visibleEntry_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeAVisibleEntryKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem visibleFirstExcess_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeAVisibleFirstExcessKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem visibleEntry_audit_commits_nonempty
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeAVisibleEntryKeys) :
    List.Forall (fun record => record.produced ≠ [])
      (ExactLedger.audit history).commits :=
  ExactLedger.audit_commits_nonempty history

/-- **The two arms of node `[93]` are distinct branches.** -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAVisibleFirstExcess) ∉
      typeAVisibleEntryKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAVisibleEntry) ∉
      typeAVisibleFirstExcessKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

/-- **Both arms carry node `[88]`'s routing and node `[89]`'s saturated
receiver.**  The exit chain and node `[94]`'s count each read `L(w)` as a
complete assignment at a receiver known to be saturated. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAReceiverRouting) ∈
      typeAVisibleEntryKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeASaturatedReceiver) ∈
      typeAVisibleFirstExcessKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

/-- **Node `[89]`'s unsaturated alternative is on neither arm.** -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAUnsaturatedReceivers) ∉
      typeAVisibleEntryKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

/-! ## The graph statements the row rests on

All four are checked at an arbitrary object, support, baseline and scale:
none knows a degree, an overload factor, or a graph family. -/

/-- **`lem:typeA-first-entry`.**  The first vertex of the support an anchored
return meets is a receiver -- proved from the definition, not assumed. -/
example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat) {receiver outside : object.Vertex}
    (return' : Graph.VisibleEntry.AnchoredReturn object receiver outside)
    (portOutside : outside ∉ support) (receiverInside : receiver ∈ support)
    (baseline : ∀ vertex ∈ support, object.degree vertex = threshold) :
    ∃ entry : object.Vertex,
      Graph.VisibleEntry.firstEntry? support return' = some entry ∧
        object.IsReceiver support threshold entry :=
  Graph.VisibleEntry.isReceiver_firstEntry return' portOutside receiverInside
    baseline

/-- **The decomposition `P = Γ ∘ Q` names that same entry.**  A receiver-entry
return's declared first-entry receiver is the vertex `ent_X` scans for, so the
two readings of `r` cannot drift apart. -/
example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    {receiver outside : object.Vertex}
    (return' : Graph.VisibleEntry.ReceiverEntryReturn object support receiver
      outside) :
    Graph.VisibleEntry.firstEntry? support return'.toAnchoredReturn =
      some return'.entry :=
  return'.firstEntry?_toAnchoredReturn

/-- **`lem:typeA-entry-budget`, degree-two entry exclusion.**  At a receiver with
a single completion port, no anchored return through it re-enters the support at
that receiver. -/
example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat) {receiver outside entry : object.Vertex}
    (return' : Graph.VisibleEntry.AnchoredReturn object receiver outside)
    (port : outside ∈ Graph.VisibleEntry.completionPorts object support receiver)
    (receiverInside : receiver ∈ support)
    (unique : object.missingPorts support threshold receiver = 1)
    (exact : object.degree receiver = threshold)
    (found : Graph.VisibleEntry.firstEntry? support return' = some entry) :
    entry ≠ receiver :=
  Graph.VisibleEntry.firstEntry_ne_of_missingPorts_eq_one return' port
    receiverInside unique exact found

/-- **`lem:typeA-entry-budget`, the budget.**  The edges through which returns
first enter the support are port edges of the other receivers, and there are at
most `Σ_{r ≠ w} q(r)` of them. -/
example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat) (receiver : object.Vertex)
    (baseline : ∀ vertex ∈ support, object.degree vertex = threshold) :
    (Graph.VisibleEntry.entryPortEdges object support threshold receiver).card ≤
      ∑ other ∈
        letI := Graph.vertexDecEq object
        (object.receivers support threshold).erase receiver,
        object.missingPorts support threshold other :=
  Graph.VisibleEntry.card_entryPortEdges_le object support threshold receiver
    baseline

/-- **`lem:typeA-silent-excess-count` at one receiver.**  With no port carrying
`s` visible returns at a saturated receiver, the visible-first order pays every
visible load and the whole excess basin is silent: `1 + L(w) ≤ |𝒰(w)| + s·q(w)`,
which is `|𝒰(w)| ≥ L(w) − c(w)` written without subtraction. -/
example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold scale : Nat) {receiver : object.Vertex}
    (exact : object.degree receiver = threshold)
    (isReceiver : object.IsReceiver support threshold receiver)
    (scalePos : 1 ≤ scale)
    (unsaturatedPorts : object.Saturated support threshold scale receiver →
      ∀ outside ∈ Graph.VisibleEntry.completionPorts object support receiver,
        (Graph.VisibleEntry.visibleLoadsAt object support threshold receiver
          outside).card + 1 ≤ scale) :
    1 + object.routedLoad support threshold receiver ≤
      (Graph.VisibleEntry.silentExcess object support threshold scale
        receiver).card +
        scale * object.missingPorts support threshold receiver :=
  Graph.VisibleEntry.one_add_routedLoad_le_silentExcess object support threshold
    scale exact isReceiver scalePos unsaturatedPorts

/-- **`lem:typeA-silent-excess-count`.**  Summed over the receivers,
`|V(X)| ≤ S_sil^exc(X) + s·def⁺(X)`, which is `S_sil^exc(X) ≥ s·D_A(X)`. -/
example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold scale : Nat) (scalePos : 1 ≤ scale)
    (baseline : ∀ vertex ∈ support, object.degree vertex = threshold)
    (capped : ∀ vertex ∈ support,
      object.internalDegree support vertex ≤ threshold)
    (routed : ∀ vertex ∈ support,
      object.internalDegree support vertex = threshold →
      ∃ receiver : object.Vertex,
        object.traceReceiver? support threshold vertex = some receiver ∧
          object.IsReceiver support threshold receiver)
    (unsaturatedPorts : ∀ receiver : object.Vertex,
      object.IsReceiver support threshold receiver →
      object.Saturated support threshold scale receiver →
      ∀ outside ∈ Graph.VisibleEntry.completionPorts object support receiver,
        (Graph.VisibleEntry.visibleLoadsAt object support threshold receiver
          outside).card + 1 ≤ scale) :
    support.card ≤
      (∑ receiver ∈ object.receivers support threshold,
          (Graph.VisibleEntry.silentExcess object support threshold scale
            receiver).card) +
        scale * object.positiveDeficiency support threshold :=
  Graph.VisibleEntry.card_le_sum_silentExcess_add_positiveDeficiency object
    support threshold scale scalePos baseline capped routed unsaturatedPorts


/-! ## `lem:typeA-port-return` and clause (Q1), at the framework level

Both are checked at an arbitrary object, receiver, port and reading: neither
knows a degree, an overload factor, or a graph family. -/

/-- **`lem:typeA-port-return`.**  `lem:bridgeless` at the port edge: a minimal
object avoiding the target carries an anchored return through every completion
port.  The two hypotheses are the two halves of the selection statement. -/
example (object : Graph.FiniteObject.{u}) (CycleLengthOK : Nat → Prop)
    (threshold : Nat) (two_le : 2 ≤ threshold)
    (baseline : Graph.MinimumDegreeAtLeast threshold object)
    (avoids : ¬ Graph.HasCycleWithLength CycleLengthOK object)
    (minimal : ∀ smaller : Graph.FiniteObject.{u},
      smaller.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast threshold smaller →
      Graph.HasCycleWithLength CycleLengthOK smaller)
    (support : Finset object.Vertex) (receiver outside : object.Vertex)
    (port : outside ∈ Graph.VisibleEntry.completionPorts object support
      receiver) :
    Nonempty (Graph.VisibleEntry.AnchoredReturn object receiver outside) :=
  Graph.VisibleEntry.exists_anchoredReturn_of_mem_completionPorts
    (LengthOK := CycleLengthOK) two_le baseline avoids minimal support receiver
    outside port

/-- **Clause (Q1) of `def:typeA-exit4-family` is generated.**  The canonical
family at an arbitrary declared reading has the visible-entry identification
among its members. -/
example (object : Graph.FiniteObject.{u}) (Target : Graph.FiniteObject.{u} → Prop)
    (Coordinate : Type u) [DecidableEq Coordinate]
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver outside : object.Vertex) (coordinates : Finset Coordinate)
    (coordinate : object.Vertex → Coordinate)
    (declared : ∀ load ∈ object.routedLoads support threshold receiver,
      coordinate load ∈ coordinates) :
    (Graph.VisibleEntry.visibleEntryFamily support threshold receiver coordinates
        coordinate outside declared).Generated
      Graph.ExitFour.ReceiverClause.visibleEntry coordinates
      (Graph.VisibleEntry.visibleCoordinates support threshold receiver
        coordinate outside coordinates) :=
  Graph.VisibleEntry.generated_visibleEntry support threshold receiver
    coordinates coordinate outside declared coordinates (subset_refl _)

/-- **(Q1)'s declared routed-load support carries the port's visible loads.**
*"In (Q1) it is the set of visible routed loads whose response coordinates are
identified."*  This is what lets exit `(4)` peel a visible load. -/
example (object : Graph.FiniteObject.{u}) (Target : Graph.FiniteObject.{u} → Prop)
    (Coordinate : Type u) [DecidableEq Coordinate]
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver outside : object.Vertex) (coordinates : Finset Coordinate)
    (coordinate : object.Vertex → Coordinate)
    (declared : ∀ load ∈ object.routedLoads support threshold receiver,
      coordinate load ∈ coordinates) :
    Graph.VisibleEntry.visibleLoadsAt object support threshold receiver
        outside ⊆
      (Graph.VisibleEntry.visibleEntryFamily support threshold receiver
          coordinates coordinate outside declared).declaredLoads
        (Graph.VisibleEntry.visibleCoordinates support threshold receiver
          coordinate outside coordinates) :=
  Graph.VisibleEntry.visibleLoadsAt_subset_declaredLoads support threshold
    receiver coordinates coordinate outside declared

/-- **The (Q1) member is nontrivial exactly when the port is visible.**  At a
port carrying a visible load the identification collapses a declared
coordinate; at a silent port the same construction collapses nothing.  This is
the branch content the yes arm commits. -/
example (object : Graph.FiniteObject.{u}) (Target : Graph.FiniteObject.{u} → Prop)
    (Coordinate : Type u) [DecidableEq Coordinate]
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver outside : object.Vertex) (coordinates : Finset Coordinate)
    (coordinate : object.Vertex → Coordinate)
    (declared : ∀ load ∈ object.routedLoads support threshold receiver,
      coordinate load ∈ coordinates)
    (seen : (Graph.VisibleEntry.visibleLoadsAt object support threshold receiver
      outside).Nonempty) :
    (Graph.VisibleEntry.visibleCoordinates support threshold receiver coordinate
      outside coordinates).Nonempty :=
  Graph.VisibleEntry.visibleCoordinates_nonempty support threshold receiver
    coordinates coordinate outside declared seen

/-! ## Immediate continuations on the same exact ledger -/

/-- Node `[91]` publishes the paper's unsaturated discharging inequality. -/
noncomputable def unsaturatedDischarge
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (dischargeFresh : K (data := data) .typeAUnsaturatedDischarge ∉ known)
  (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (residualCTypeAUnsaturatedReceiverKeys known)) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      (residualCTypeAUnsaturatedDischargeKeys known) :=
  (typeAUnsaturatedDischargeRow (BranchState := BranchState)
    (presentation := presentation) (data := data)
    (K .typeAReceiverRouting)
    (K .typeAUnsaturatedReceivers) (K .typeAUnsaturatedDischarge) (by simp)
    (fun _input fact => fact.down) (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)).run history (by
      simp [residualCTypeAUnsaturatedReceiverKeys, dischargeFresh])

/-- The new node `[91]` fact closes against the negative Type A support already
present in the same ancestry. -/
noncomputable def unsaturatedClosed
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (dischargeFresh : K (data := data) .typeAUnsaturatedDischarge ∉ known)
    (closedFresh : closed ∉ known)
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (residualCTypeAUnsaturatedReceiverKeys known)) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      (residualCTypeAUnsaturatedClosedKeys known) :=
  closeIncompatible (unsaturatedDischarge dischargeFresh history)
    (K .typeALowSurplus) (K .typeAUnsaturatedDischarge) (by
      simp [residualCTypeAUnsaturatedDischargeKeys,
        residualCTypeAUnsaturatedReceiverKeys, closedFresh])

/-- Node `[93]`'s visible arm advances through exactly exit `(1)` at `[95]`. -/
noncomputable def visibleExitOne
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .returnAvoidance) known]
    (returnFresh : K (data := data) .typeAExitOneReturn ∉ known)
    (freeFresh : K (data := data) .typeAExitOneFree ∉ known)
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (residualCTypeAVisibleEntryKeys known)) :
    Decision (K .typeAExitOneReturn) (K .typeAExitOneFree) history :=
  typeAExitOneDichotomy history (K .typeAVisibleEntry)
    (K .typeAExitOneReturn) (K .typeAExitOneFree) (fun fact => fact.down)
    (fun value => ⟨value⟩) (fun value => ⟨value⟩)
    (by simp [residualCTypeAVisibleEntryKeys, returnFresh])
    (by simp [residualCTypeAVisibleEntryKeys, freeFresh])

theorem unsaturatedClosed_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (residualCTypeAUnsaturatedClosedKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

end Hypostructure.Fixtures.TypeAVisibleEntry
