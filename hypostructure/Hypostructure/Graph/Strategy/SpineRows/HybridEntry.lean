import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Certificate

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Nodes `[72]`/`[81]`, the local B1 fan ledger (`lem:typeB-hybrid-incidence-budget`,
`lem:typeB-hybrid-B1`) at every certificate-marked assigned centre. -/
@[reducible] noncomputable def hybridEntryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.hybridEntry
    { Requires := [K .selection, K .fanCertificateMarked, K .fanCertificateCap]
      Produces := [K .typeBHybridEntry]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBHybridEntry)
        ⟨Contracts.TypeB.typeBFanHybridEntry (inputs.get (K .selection)).down.1
          data.quadrilateralAccepted data.three_le_threshold data.fanCapSlack
          data.highCentreDeficitSlack (inputs.get (K .fanCertificateMarked)).down
          (inputs.get (K .fanCertificateCap)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
