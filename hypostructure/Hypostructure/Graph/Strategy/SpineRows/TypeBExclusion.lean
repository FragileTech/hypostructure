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

/-- Nodes `[74]`/`[82]`, `prop:typeB-bridge-reduction` on the canonical B2 ledger
of the Type B support read from `K .typeBDisjointLedger`: a nonnegative
remaining core gives `N₀(Y_X) ≥ 0`. -/
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

/-- Nodes `[74]` → `[76]` / `[82]` → `[85]`: Type B cannot carry the linear deficit
outside route `8`.  On the B2-paid support the negative post-ledger core of its
canonical B2 ledger (read from `K .typeBDisjointLedger` and `K .typeBExcluded`)
carries the deficit only through the route-`8` residual `[77]`. -/
@[reducible] noncomputable def typeBExclusionResidualRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBExclusionResidual
    { Requires := [K .typeBDisjointLedger, K .typeBExcluded, K .cubicBaseline]
      Produces := [K .typeBExclusionResidual]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBExclusionResidual)
        ⟨Contracts.TypeB.typeBExclusionResidual
          (inputs.get (K .cubicBaseline)).down.2.2.2.2.2.2.2.2
          (inputs.get (K .typeBDisjointLedger)).down
          (inputs.get (K .typeBExcluded)).down⟩
        .nil)

/-- Nodes `[75]` → `[76]` / `[84]` → `[85]` on the certificate-residual arm: the
fan-certificate residual support (read from `K .fanCertificateResidualMass`) is
a Type B bridge residual whose assigned centres are charged to their surplus. -/
@[reducible] noncomputable def typeBCertificateMassExclusionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBCertificateMassExclusion
    { Requires := [K .fanCertificateResidualMass, K .selection, K .uncompressible,
        K .remainderNormalized, K .cubicBaseline]
      Produces := [K .typeBExclusionResidual]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBExclusionResidual)
        ⟨Contracts.TypeB.typeBExclusionResidual_of_fanMass
          (inputs.get (K .selection)).down.1
          (fun vertex => le_trans inputs.current.baseline
            (inputs.current.object.minDegree_le_degree vertex))
          (inputs.get (K .uncompressible)).down
          (inputs.get (K .remainderNormalized)).down
          (inputs.get (K .cubicBaseline)).down.2.2.2.2.2.2.2.2
          (inputs.get (K .fanCertificateResidualMass)).down⟩
        .nil)

/-- Nodes `[75]` → `[76]` / `[84]` → `[85]` on the B2-failure arm: the obstructed
support (read from `K .typeBOverlapObstructionMass`) is a Type B bridge residual
whose assigned centres are charged to their surplus. -/
@[reducible] noncomputable def typeBObstructionMassExclusionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBObstructionMassExclusion
    { Requires := [K .typeBOverlapObstructionMass, K .selection, K .uncompressible,
        K .remainderNormalized, K .cubicBaseline]
      Produces := [K .typeBExclusionResidual]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBExclusionResidual)
        ⟨Contracts.TypeB.typeBExclusionResidual_of_fanMass
          (inputs.get (K .selection)).down.1
          (fun vertex => le_trans inputs.current.baseline
            (inputs.current.object.minDegree_le_degree vertex))
          (inputs.get (K .uncompressible)).down
          (inputs.get (K .remainderNormalized)).down
          (inputs.get (K .cubicBaseline)).down.2.2.2.2.2.2.2.2
          (inputs.get (K .typeBOverlapObstructionMass)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
