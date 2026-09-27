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

/-- **Nodes `[72]`/`[81]`, the direct fan-window cycles inside the local
fan-window ledger** (`lem:typeB-direct-fan-window-cycles`,
`lem:typeB-two-window-cycles`): at the marked Type B support every assigned
centre is direct-cycle free at `P₀`, since a direct configuration builds a cycle
of accepted length, which the selection denies.  The paper excludes these
cycles inside `[72]`; there is no separate diamond. -/
@[reducible] noncomputable def typeBDirectCycleFreeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBDirectCycleFree
    { Requires := [K .fanCertificateMarked, K .selection]
      Produces := [K .typeBDirectCycleFree]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBDirectCycleFree)
        ⟨Contracts.TypeB.typeBFanDirectCycleFree (inputs.get (K .selection)).down.1
          (inputs.get (K .fanCertificateMarked)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
