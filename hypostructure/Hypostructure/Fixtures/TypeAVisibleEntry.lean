import Hypostructure.Graph.Strategy.SpineRun

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

/-! ## Node `[93]`, asked on the saturated cursor -/

/-- **The visible-entry question, asked on the cursor node `[89]` left.**

Both prerequisites -- node `[88]`'s routing and node `[89]`'s saturated receiver
-- are discharged by instance resolution against the incoming index, and the two
freshness side conditions are decided on the vocabulary's own finite `Key`. -/
noncomputable def visibleEntry
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeASaturatedReceiverKeys) :
    Decision (K .typeAVisibleEntry) (K .typeAVisibleFirstExcess) history :=
  typeAVisibleEntryDichotomy history (K .typeAReceiverRouting)
    (K .typeASaturatedReceiver) (K .typeAVisibleEntry)
    (K .typeAVisibleFirstExcess)
    (fun fact packing valid maximal piece inside surplus =>
      (fact.down packing valid maximal piece inside surplus).1)
    (fun fact => fact.down) (fun visible => ⟨visible⟩)
    (fun excess => ⟨excess⟩) (by simp) (by simp)

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
        (Graph.VisibleEntry.receivers object support threshold).erase receiver,
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
      (∑ receiver ∈ Graph.VisibleEntry.receivers object support threshold,
          (Graph.VisibleEntry.silentExcess object support threshold scale
            receiver).card) +
        scale * object.positiveDeficiency support threshold :=
  Graph.VisibleEntry.card_le_sum_silentExcess_add_positiveDeficiency object
    support threshold scale scalePos baseline capped routed unsaturatedPorts

end Hypostructure.Fixtures.TypeAVisibleEntry
