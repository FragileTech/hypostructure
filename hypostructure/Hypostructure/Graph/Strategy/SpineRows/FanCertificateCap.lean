import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Local

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[70]`: the fan-safe graph (`def:typeB-fan-safe` (i), forced by the
selection) and the certificate-marked cap `d_G(h) ≤ α(D)` of
`lem:fan-certificate`, a structural consequence of the label algebra, at every
assigned centre. -/
@[reducible] noncomputable def fanCertificateCapRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.fanCertificateCap
    { Requires := [K .selection]
      Produces := [K .fanCertificateCap]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .fanCertificateCap)
        ⟨Contracts.TypeB.typeBFanCertificateCap (inputs.get (K .selection)).down.1⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
