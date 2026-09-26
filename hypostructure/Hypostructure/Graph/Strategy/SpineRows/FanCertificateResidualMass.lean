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

/-- Nodes `[71]` → `[75]`, `[80]` → `[84]`: fan-certificate residual centres charged
to assigned surplus. -/
@[reducible] noncomputable def fanCertificateResidualMassRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.fanCertificateResidualMass
    { Requires := [K .fanCertificateResidual]
      Produces := [K .fanCertificateResidualMass]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .fanCertificateResidualMass)
        ⟨Contracts.TypeB.typeBFanCertificateResidualMass data.bridgeMassSlack
          (inputs.get (K .fanCertificateResidual)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
