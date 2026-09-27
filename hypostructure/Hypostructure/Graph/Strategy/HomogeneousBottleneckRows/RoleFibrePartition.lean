import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic
import Hypostructure.Graph.SparseUpperEnvelope
import Hypostructure.Graph.Contracts.SurplusPair.Pressure

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[137]`, first production: `lem:exact-surplus-pair-charge-partition`
with `thm:sharp-classwise-homogeneous-token-budget` (a)--(c) and
`thm:sharp-surplus-overload-audit` (b)--(c), for the literal presentation and
free-side entropy count already written to the incoming ledger. -/
@[reducible] noncomputable def roleFibrePartitionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.roleFibrePartition
    { Requires := [K .blockedPairEntropySandwich, K .canonicalPairLedger,
        K .sparseSlackSurplus, K .surplusAbove]
      Produces := [K .roleFibrePartition]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .roleFibrePartition)
        ⟨Graph.Contracts.SurplusPair.roleFibrePartition_of_sandwich
          (inputs.get (K .blockedPairEntropySandwich)).down
          (inputs.get (K .canonicalPairLedger)).down
          (inputs.get (K .sparseSlackSurplus)).down
          (inputs.get (K .surplusAbove)).down
          data.three_le_threshold⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
