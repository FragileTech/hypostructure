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

/-- Node `[70]` on the heavy arm, after `[69]`: the fan-safe graph
(`def:typeB-fan-safe` (i), forced by the selection) and the certificate-marked
cap `d_G(h) ≤ α(D)` of `lem:fan-certificate` at every assigned centre of the
Type B support of the `[69]` fact (`K .typeBFanLocalDichotomy`). -/
@[reducible] noncomputable def fanCertificateCapRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.fanCertificateCap
    { Requires := [K .typeBFanLocalDichotomy, K .selection]
      Produces := [K .fanCertificateCap]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .fanCertificateCap)
        ⟨Contracts.TypeB.typeBFanCertificateCap (inputs.get (K .selection)).down.1
          (inputs.get (K .typeBFanLocalDichotomy)).down⟩
        .nil)

/-- Node `[70]` on the degree-four arm, after `[79]`: the fan-safe graph and the
certificate-marked cap at every assigned centre of the Type B support of the
`[79]` fact (`K .typeBFanDegreeFourProfile`). -/
@[reducible] noncomputable def degreeFourFanCertificateCapRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.degreeFourFanCertificateCap
    { Requires := [K .typeBFanDegreeFourProfile, K .selection]
      Produces := [K .fanCertificateCap]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .fanCertificateCap)
        ⟨Contracts.TypeB.typeBFanCertificateCap (inputs.get (K .selection)).down.1
          (inputs.get (K .typeBFanDegreeFourProfile)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
