import Hypostructure.Graph.Strategy.SpineRun

/-!
# Fixture: nodes `[74]`/`[82]`, `[73]`/`[75]`, `[83]`/`[84]`, `[76]`/`[85]`

The three rows that close the Type B fan branch -- the hybrid B1 entry, the
bridge fan-mass estimate, and Step 1 of the Type B exclusion -- are quantified
over the keys they commit and carry no predecessor parameter.  This fixture
installs each of them at the spine's own vocabulary, on every canonical cursor
the manuscript enters it from, and checks what the audit's four columns claim:

* each row elaborates only against a cursor whose index already carries its
  declared requirements, so none of them can be run before the branch reached
  the node the manuscript enters them from;
* the fan-mass row is *one* value at four positions and the exclusion-charge row
  *one* value at two, so neither manuscript position duplicates a registration;
* the bridge-residual indices and the B1 indices are disjoint -- neither carries
  the other's fact -- which is the type-level statement that the fan-mass
  estimate cannot be read on the arm that paid locally, nor the closed
  neighbourhood charge on the arm that did not;
* every exit's audit lists exactly the facts that branch committed, in commit
  order, with none duplicated and none archived.

Nothing here is specific to one manuscript: the rows run at the framework's own
`Spine.Data`, left as a parameter.
-/

namespace Hypostructure.Fixtures.TypeBBridgeNode

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[74]`/`[82]`: the hybrid B1 entry, at both B2 cursors -/

/-- **`[74]`**: the B1 payment on the heavy arm's B2 cursor. -/
noncomputable def hybridEntryAtSeventyFour
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBDisjointAssignmentKeys) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      typeBHybridEntryKeys :=
  (hybridEntry (data := data)).run history (by simp)

/-- **`[82]`**: the *same executor value*, after the degree-four B2 cursor. -/
noncomputable def hybridEntryAtEightyTwo
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourDisjointAssignmentKeys) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      degreeFourHybridEntryKeys :=
  (hybridEntry (data := data)).run history (by simp)

/-! ## Nodes `[73]`/`[75]` and `[83]`/`[84]`: the fan-mass row, at four cursors -/

/-- **`[75]`**, entered from `[71]`'s no arm: a fan-certificate residual centre. -/
noncomputable def fanMassAtSeventyFive
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBCertificateResidualKeys) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      typeBCertificateResidualMassKeys :=
  (bridgeFanMass (data := data)).run history (by simp)

/-- **`[75]`**, entered from `[73]`: a B2 disjoint-carrier failure. -/
noncomputable def fanMassAtSeventyThree
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBOverlapObstructionKeys) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      typeBOverlapObstructionMassKeys :=
  (bridgeFanMass (data := data)).run history (by simp)

/-- **`[84]`**, entered from `[80]`'s no arm. -/
noncomputable def fanMassAtEightyFour
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourResidualKeys) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      degreeFourResidualMassKeys :=
  (bridgeFanMass (data := data)).run history (by simp)

/-- **`[84]`**, entered from `[83]`. -/
noncomputable def fanMassAtEightyThree
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourOverlapObstructionKeys) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      degreeFourOverlapObstructionMassKeys :=
  (bridgeFanMass (data := data)).run history (by simp)

/-! ## Nodes `[76]`/`[85]`: Step 1 of the exclusion, at both B1 cursors -/

/-- **`[76]`**: the closed-neighbourhood charge after `[74]`. -/
noncomputable def exclusionChargeAtSeventySix
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBHybridEntryKeys) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      typeBExclusionChargeKeys :=
  (typeBExclusionCharge (data := data)).run history (by simp)

/-- **`[85]`**: the *same executor value*, after `[82]`. -/
noncomputable def exclusionChargeAtEightyFive
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourHybridEntryKeys) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      degreeFourExclusionChargeKeys :=
  (typeBExclusionCharge (data := data)).run history (by simp)

/-! ## The branch separation the manuscript's routing depends on -/

/-- **The bridge-mass fact is absent from every B1 index.**  `[76]`'s cursor paid
its fans locally, so it cannot read the residual-mass estimate. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeBBridgeMass) ∉
      typeBExclusionChargeKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeBBridgeMass) ∉
      degreeFourExclusionChargeKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

/-- **The closed-neighbourhood charge is absent from every bridge-residual
index.**  A bridge residual has no certificate-closed local entry to charge, so
Step 1 of the exclusion is not available on those arms. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeBExclusionCharge) ∉
      typeBCertificateResidualMassKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeBExclusionCharge) ∉
      typeBOverlapObstructionMassKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

/-- **The two fan-mass entries stay distinct.**  `[75]` from `[71]` carries the
fan-certificate residual; `[75]` from `[73]` carries the overlap obstruction and
the direct-cycle-free ledger.  Neither carries the other's fact. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeBOverlapObstruction) ∉
      typeBCertificateResidualMassKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .fanCertificateResidual) ∉
      typeBOverlapObstructionMassKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

/-! ## Every exit's audit is complete, unique and commit-forced -/

theorem exclusionCharge_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBExclusionChargeKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem degreeFourExclusionCharge_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourExclusionChargeKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem certificateResidualMass_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBCertificateResidualMassKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem overlapObstructionMass_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBOverlapObstructionMassKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem degreeFourResidualMass_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourResidualMassKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem degreeFourOverlapObstructionMass_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourOverlapObstructionMassKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

/-- **No exit commits an empty record.**  Each of the three rows produces exactly
one fact, so every commit on these branches carries one. -/
theorem exclusionCharge_audit_commits_nonempty
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBExclusionChargeKeys) :
    List.Forall (fun record => record.produced ≠ [])
      (ExactLedger.audit history).commits :=
  ExactLedger.audit_commits_nonempty history

theorem certificateResidualMass_audit_commits_nonempty
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBCertificateResidualMassKeys) :
    List.Forall (fun record => record.produced ≠ [])
      (ExactLedger.audit history).commits :=
  ExactLedger.audit_commits_nonempty history

/-! ## Nodes `[76]`/`[85]`: `thm:branch-kill` (b) -/

/-- **`[76]`**: the exclusion question, on the cursor `[74]` leaves. -/
noncomputable def branchKillAtSeventySix
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBExclusionChargeKeys) :
    Decision (K .typeBExcluded) (K .typeBExclusionResidual) history :=
  typeBExclusionDichotomy history (K .typeBExclusionCharge) (K .typeBExcluded)
    (K .typeBExclusionResidual)
    (fun fact packing valid piece inside connected charge positive =>
      (fact.down packing valid piece inside connected charge positive).2)
    (fun excluded => ⟨excluded⟩) (fun residual => ⟨residual⟩) (by simp) (by simp)

/-- **`[85]`**: the *same* `Decision` value, after the degree-four cursor. -/
noncomputable def branchKillAtEightyFive
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourExclusionChargeKeys) :
    Decision (K .typeBExcluded) (K .typeBExclusionResidual) history :=
  typeBExclusionDichotomy history (K .typeBExclusionCharge) (K .typeBExcluded)
    (K .typeBExclusionResidual)
    (fun fact packing valid piece inside connected charge positive =>
      (fact.down packing valid piece inside connected charge positive).2)
    (fun excluded => ⟨excluded⟩) (fun residual => ⟨residual⟩) (by simp) (by simp)

/-- **The closing arm really closes.**  `closeIncompatible` consumes the
node-`[64]` residual's negative net charge and the exclusion's nonnegative one and
appends the reserved closure key; the resulting index is node `[76]`'s closed
terminal. -/
noncomputable def closeBranchKill
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (K .typeBExcluded :: typeBExclusionChargeKeys)) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      typeBBranchKillKeys :=
  closeIncompatible history (K .typeBHighSurplus) (K .typeBExcluded) (by simp)

/-- **Neither arm of `thm:branch-kill` (b) is visible on the other.** -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeBExcluded) ∉
      typeBExclusionResidualKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeBExclusionResidual) ∉
      typeBBranchKillKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) := by
  simp

theorem branchKill_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBBranchKillKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

end Hypostructure.Fixtures.TypeBBridgeNode
