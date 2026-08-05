import Hypostructure.Graph.Strategy.SpineRun

/-!
# Fixture: node `[72]`, both halves, at both of its positions

The two rows of node `[72]` -- the direct fan-window cycle removal and the B2
B2 disjoint-carrier question -- are quantified over the keys they commit.  This
fixture installs them at the spine's *own* vocabulary, on the ledger the
certificate-marked arm of node `[71]` leaves, and checks the four things the
audit's Ledger, Transport, Residual and Facts columns claim:

* each row elaborates only as a `Decision` against the literal incoming branch
  cursor, so neither can be run on a history that has not reached node `[71]`'s
  yes arm;
* the arm not taken is absent from the taken branch's key index -- there are
  exactly two output indices per row, and they differ in one entry;
* the closing arm really closes: the registered incompatibility between the
  selection and the direct-cycle fact produces the reserved closure entry,
  which no row of the vocabulary can spell;
* the audit of each of the three exits lists exactly the facts that branch
  committed, in commit order, with no fact archived to make room.

Nothing here is specific to one manuscript: the rows run at the framework's own
`Spine.Data`, left as a parameter.
-/

namespace Hypostructure.Fixtures.TypeBFanWindowNode

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[72]`, first half -/

/-- **The direct-cycle question, asked on the certificate-marked cursor.**

The freshness side conditions are decided on the vocabulary's own finite `Key`,
and the incoming index is the literal one node `[71]`'s yes arm produced -- the
row reconstructs no cursor and re-reads no root. -/
noncomputable def directCycle
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBCertificateMarkedKeys) :
    Decision (K .typeBDirectCycle) (K .typeBDirectCycleFree) history :=
  directCycleDichotomy history (K .typeBDirectCycle) (K .typeBDirectCycleFree)
    (fun present => ⟨present⟩) (fun free => ⟨free⟩) (by simp) (by simp)

/-- **The closing arm closes.**  `closeIncompatible` consumes the selection's
avoidance and the direct-cycle fact and appends the reserved closure key; the
resulting index is exactly node `[72]`'s closed terminal. -/
noncomputable def closeDirectCycle
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (K .typeBDirectCycle :: typeBCertificateMarkedKeys)) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      typeBDirectCycleClosedKeys :=
  closeIncompatible history (K .selection) (K .typeBDirectCycle) (by simp)

/-! ## Node `[72]`/`[81]`, second half -/

/-- **The B2 question, asked on the direct-cycle-free cursor.** -/
noncomputable def b2Assignment
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBDirectCycleFreeKeys) :
    Decision (K .typeBDisjointAssignment) (K .typeBOverlapObstruction) history :=
  b2AssignmentDichotomy history (K .typeBDisjointAssignment)
    (K .typeBOverlapObstruction) (fun assignment => ⟨assignment⟩)
    (fun obstruction => ⟨obstruction⟩) (by simp) (by simp)

/-! ## What the three exits carry

Each exit's audit is checked against its own key index, so an omitted or
duplicated commit would fail to elaborate. -/

theorem directCycleClosed_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBDirectCycleClosedKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem disjointAssignment_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBDisjointAssignmentKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem overlapObstruction_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBOverlapObstructionKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-- **No exit commits a semantic fact twice**, including the closed one: the
closure entry is the reserved key, not a second copy of a fact. -/
theorem directCycleClosed_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBDirectCycleClosedKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem disjointAssignment_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBDisjointAssignmentKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem overlapObstruction_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBOverlapObstructionKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

/-- **The two arms of the B2 question are distinct branches.**  The
disjoint-assignment index does not contain the obstruction key and conversely, which
is the type-level statement that the fan-mass row cannot read the assignment nor the
bridge-reduction row the obstruction. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeBOverlapObstruction) ∉
      typeBDisjointAssignmentKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeBDisjointAssignment) ∉
      typeBOverlapObstructionKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

/-- **Neither arm of node `[72]`'s first half is visible on the other.** -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeBDirectCycle) ∉
      typeBDirectCycleFreeKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

/-! ## The second position: nodes `[80]` and `[81]`

`[72]`/`[81]` and `[71]`/`[80]` are one row each at two positions.  Because a
`Decision` carries no predecessor, the *same three values* run after the
degree-four cursor; this section installs them there and checks that they do.
Nothing is re-registered, and no second copy of any row exists. -/

/-- **The certificate question at `[80]`**: the row of `[71]`, on the
degree-four profile cursor. -/
noncomputable def degreeFourCertificate
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBDegreeFourProfileKeys) :
    Decision (K .fanCertificateMarked) (K .fanCertificateResidual) history :=
  fanCertificateDichotomy history (K .fanCertificateMarked)
    (K .fanCertificateResidual) (fun marked => ⟨marked⟩)
    (fun residual => ⟨residual⟩) (by simp) (by simp)

/-- **The direct-cycle question at `[81]`**: the row of `[72]`'s first half, on
the degree-four marked cursor. -/
noncomputable def degreeFourDirectCycle
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourMarkedKeys) :
    Decision (K .typeBDirectCycle) (K .typeBDirectCycleFree) history :=
  directCycleDichotomy history (K .typeBDirectCycle) (K .typeBDirectCycleFree)
    (fun present => ⟨present⟩) (fun free => ⟨free⟩) (by simp) (by simp)

/-- **The B2 question at `[81]`**: the row of `[72]`'s second half, on the
degree-four direct-cycle-free cursor. -/
noncomputable def degreeFourB2
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourDirectCycleFreeKeys) :
    Decision (K .typeBDisjointAssignment) (K .typeBOverlapObstruction) history :=
  b2AssignmentDichotomy history (K .typeBDisjointAssignment)
    (K .typeBOverlapObstruction) (fun assignment => ⟨assignment⟩)
    (fun obstruction => ⟨obstruction⟩) (by simp) (by simp)

/-- **The two positions are disjoint branches.**  Node `[81]`'s indices carry
`typeBDegreeFourCentres` and node `[72]`'s carry `typeBHeavyCentre`; neither
carries the other, so no fact of one position is visible at the other even though
the rows are the same values. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeBHeavyCentre) ∉
      degreeFourDisjointAssignmentKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeBDegreeFourCentres) ∉
      typeBDisjointAssignmentKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

/-- **`[79]`'s profile is on every degree-four exit.**  The B2 arms of `[81]`
carry the profile fact, which is what lets `[82]` read the deficit without
re-deriving it. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeBDegreeFourProfile) ∈
      degreeFourOverlapObstructionKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

end Hypostructure.Fixtures.TypeBFanWindowNode
