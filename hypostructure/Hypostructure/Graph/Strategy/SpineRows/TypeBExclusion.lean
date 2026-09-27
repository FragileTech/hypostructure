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

/-- Node `[74]`, `prop:typeB-bridge-reduction` on the canonical B2 ledger of the
Type B support read from `K .typeBDisjointLedger`: its remaining core carries
the whole deficit, so a nonnegative remaining core gives `N₀(X) ≥ 0`. -/
@[reducible] noncomputable def typeBExcludedRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBExcluded
    { Requires := [K .typeBDisjointLedger]
      Produces := [K .typeBExcluded]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBExcluded)
        ⟨Contracts.TypeB.typeBExcluded (inputs.get (K .typeBDisjointLedger)).down⟩
        .nil)

/-- Node `[74]` → `[76]`: Type B cannot carry the linear deficit outside route
`8`; the B2-paid support (`K .typeBDisjointLedger`) keeps its whole deficit in
the remaining core of its canonical B2 ledger (`K .typeBExcluded`). -/
@[reducible] noncomputable def typeBExclusionResidualRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBExclusionResidual
    { Requires := [K .typeBDisjointLedger, K .typeBExcluded]
      Produces := [K .typeBExclusionResidual]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBExclusionResidual)
        ⟨Contracts.TypeB.typeBExclusionResidual
          (inputs.get (K .typeBDisjointLedger)).down
          (inputs.get (K .typeBExcluded)).down⟩
        .nil)

/-- Nodes `[75]` → `[76]` / `[84]` → `[85]` on the certificate-residual arm:
the fan-certificate residual support (`K .fanCertificateResidualMass`) fails
B2 and its negative part is charged to its assigned surplus. -/
@[reducible] noncomputable def typeBCertificateMassExclusionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBCertificateMassExclusion
    { Requires := [K .fanCertificateResidualMass]
      Produces := [K .typeBExclusionResidual]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBExclusionResidual)
        ⟨Contracts.TypeB.typeBExclusionResidual_of_certificateMass
          (inputs.get (K .fanCertificateResidualMass)).down⟩
        .nil)

/-- Nodes `[75]` → `[76]` / `[84]` → `[85]` on the B2-failure arm: the obstructed
support (`K .typeBOverlapObstructionMass`) fails B2 at G's canonical obstruction
and its negative part is charged to its assigned surplus. -/
@[reducible] noncomputable def typeBObstructionMassExclusionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBObstructionMassExclusion
    { Requires := [K .typeBOverlapObstructionMass]
      Produces := [K .typeBExclusionResidual]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBExclusionResidual)
        ⟨Contracts.TypeB.typeBExclusionResidual_of_obstructionMass
          (inputs.get (K .typeBOverlapObstructionMass)).down⟩
        .nil)

/-- Node `[82]` → `[85]`: the certificate-closed or B2-paid support
(`K .typeBDegreeFourClosed`) keeps its deficit in the remaining core of its
canonical B2 ledger, or, B2 failing at it, is a Type B bridge residual charged
to its assigned surplus. -/
@[reducible] noncomputable def typeBDegreeFourExclusionResidualRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBDegreeFourExclusionResidual
    { Requires := [K .typeBDegreeFourClosed, K .selection, K .uncompressible,
        K .remainderNormalized, K .cubicBaseline]
      Produces := [K .typeBExclusionResidual]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBExclusionResidual)
        ⟨Contracts.TypeB.typeBExclusionResidual_of_degreeFourClosed
          (inputs.get (K .selection)).down.1
          (fun vertex => le_trans inputs.current.baseline
            (inputs.current.object.minDegree_le_degree vertex))
          (inputs.get (K .uncompressible)).down
          (inputs.get (K .remainderNormalized)).down
          (inputs.get (K .cubicBaseline)).down.2.1.2.2.2.2
          (inputs.get (K .typeBDegreeFourClosed)).down⟩
        .nil)

/-- Node `[76]`/`[85]` → `[77]`: the Type B entry into route `8`.  A negative
Type B support hands the negative remaining core of its canonical B2 ledger to
route `8`, or is a bridge residual charged to its surplus
(`K .typeBExclusionResidual`). -/
@[reducible] noncomputable def typeBRoute8EntryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBRoute8Entry
    { Requires := [K .typeBExclusionResidual]
      Produces := [K .typeBRoute8Entry]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBRoute8Entry)
        ⟨Contracts.TypeB.typeBRoute8Entry
          (inputs.get (K .typeBExclusionResidual)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
