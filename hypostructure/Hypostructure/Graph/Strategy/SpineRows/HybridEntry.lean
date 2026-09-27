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
`lem:typeB-hybrid-B1`) at every assigned centre of the direct-cycle-free,
certificate-marked Type B support. -/
@[reducible] noncomputable def hybridEntryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.hybridEntry
    { Requires := [K .selection, K .typeBDirectCycleFree, K .cubicBaseline]
      Produces := [K .typeBHybridEntry]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBHybridEntry)
        ⟨Contracts.TypeB.typeBFanHybridEntry (inputs.get (K .selection)).down.1
          (inputs.get (K .cubicBaseline)).down.2.1.1 (le_of_eq (inputs.get (K .cubicBaseline)).down.1.1.symm)
          (inputs.get (K .cubicBaseline)).down.2.1.2.2.1
          (inputs.get (K .cubicBaseline)).down.2.1.2.2.2.1 (inputs.get (K .typeBDirectCycleFree)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
