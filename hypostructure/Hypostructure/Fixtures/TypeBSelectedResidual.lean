import Hypostructure.Graph.Strategy.SpineRows

/-!
# Fixture: exact selected Type B residual through nodes `[68]`--`[82]`

This fixture instantiates the Type B Decisions and dependent fact-only rows on
one literal `ExactLedger`.  Both arms retain node `[62]`'s key-52 canonical
packing/component/piece fact; no row quantifies over or reconstructs another
support.
-/

namespace Hypostructure.Fixtures.TypeBSelectedResidual

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

abbrev baseKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  [K .fanCertificateCap, K .highCentreNormalForm, K .typeBHighSurplus,
    K .selection]

abbrev heavyKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBHeavyCentre :: baseKeys

abbrev degreeFourKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBDegreeFourCentres :: baseKeys

abbrev localKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBLocalDichotomy :: heavyKeys

abbrev profileKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBDegreeFourProfile :: degreeFourKeys

abbrev heavyMarkedKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .fanCertificateMarked :: localKeys

abbrev degreeFourMarkedKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .fanCertificateMarked :: profileKeys

noncomputable def heavySplit
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected baseKeys) :
    Decision (K .typeBHeavyCentre) (K .typeBDegreeFourCentres) history :=
  heavyCentreDichotomy (BranchState := BranchState)
    (Presentation := Presentation) (presentation := presentation) (data := data)
    history (K .typeBHighSurplus)
    (K .typeBHeavyCentre) (K .typeBDegreeFourCentres)
    (fun fact => fact.down) (fun fact => ⟨fact⟩) (fun fact => ⟨fact⟩)
    (by simp) (by simp)

noncomputable def heavyLocal
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected heavyKeys) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      localKeys :=
  (heavyCentreLocalDichotomyRow (BranchState := BranchState)
    (Presentation := Presentation) (presentation := presentation) (data := data)
    (K .highCentreNormalForm)
    (K .typeBHeavyCentre) (K .typeBLocalDichotomy) (by simp)
    (fun _ fact => fact.down) (fun _ fact => fact.down)
    (fun _ fact => ⟨fact⟩)).run history (by simp)

noncomputable def degreeFourProfile
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourKeys) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      profileKeys :=
  (degreeFourProfileRow (BranchState := BranchState)
    (Presentation := Presentation) (presentation := presentation) (data := data)
    (K .highCentreNormalForm)
    (K .typeBDegreeFourCentres) (K .typeBDegreeFourProfile) (by simp)
    (fun _ fact => fact.down) (fun _ fact => fact.down)
    (fun _ fact => ⟨fact⟩)).run history (by simp)

noncomputable def heavyCertificateSplit
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected localKeys) :
    Decision (K .fanCertificateMarked) (K .fanCertificateResidual) history :=
  fanCertificateDichotomy (BranchState := BranchState)
    (Presentation := Presentation) (presentation := presentation) (data := data)
    history (K .typeBHighSurplus)
    (K .fanCertificateMarked) (K .fanCertificateResidual)
    (fun fact => fact.down) (fun fact => ⟨fact⟩) (fun fact => ⟨fact⟩)
    (by simp) (by simp)

noncomputable def degreeFourCertificateSplit
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected profileKeys) :
    Decision (K .fanCertificateMarked) (K .fanCertificateResidual) history :=
  fanCertificateDichotomy (BranchState := BranchState)
    (Presentation := Presentation) (presentation := presentation) (data := data)
    history (K .typeBHighSurplus)
    (K .fanCertificateMarked) (K .fanCertificateResidual)
    (fun fact => fact.down) (fun fact => ⟨fact⟩) (fun fact => ⟨fact⟩)
    (by simp) (by simp)

noncomputable def heavyHybridEntry
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected heavyMarkedKeys) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      (K .typeBHybridEntry :: heavyMarkedKeys) :=
  (hybridEntryRow (BranchState := BranchState)
    (Presentation := Presentation) (presentation := presentation) (data := data)
    (K .selection) (K .fanCertificateCap)
    (K .fanCertificateMarked) (K .typeBHybridEntry)
    (by simp) (by simp) (by simp) (fun _ fact => fact.down.1)
    (fun _ fact => fact.down) (fun _ fact => fact.down)
    (fun _ fact => ⟨fact⟩)).run history (by simp)

noncomputable def degreeFourHybridEntry
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourMarkedKeys) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      (K .typeBHybridEntry :: degreeFourMarkedKeys) :=
  (hybridEntryRow (BranchState := BranchState)
    (Presentation := Presentation) (presentation := presentation) (data := data)
    (K .selection) (K .fanCertificateCap)
    (K .fanCertificateMarked) (K .typeBHybridEntry)
    (by simp) (by simp) (by simp) (fun _ fact => fact.down.1)
    (fun _ fact => fact.down) (fun _ fact => fact.down)
    (fun _ fact => ⟨fact⟩)).run history (by simp)

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeBHighSurplus) ∈
      (K .typeBHybridEntry :: heavyMarkedKeys) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeBHighSurplus) ∈
      (K .typeBHybridEntry :: degreeFourMarkedKeys) := by
  simp

theorem heavyHybrid_audit_complete
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (K .typeBHybridEntry :: heavyMarkedKeys)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem degreeFourHybrid_audit_complete
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (K .typeBHybridEntry :: degreeFourMarkedKeys)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

end Hypostructure.Fixtures.TypeBSelectedResidual
