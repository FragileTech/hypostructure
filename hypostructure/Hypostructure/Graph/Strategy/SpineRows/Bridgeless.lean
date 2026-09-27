import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.NetCharge

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## `lem:bridgeless`: the selected object has no bridge

*"The graph `G` has no bridge.  Consequently every edge of `G` lies on a
cycle; equivalently, `R_e(G) ≠ ∅` for every oriented edge."*  The manuscript's
proof contracts a bridge into a smaller counterexample; that is the framework's
`Graph.EdgeContraction.hasReturn_of_minimal`, whose two hypotheses are the two
halves of the selection fact and whose degree side condition is the standing
baseline.  The row reads `K .selection` and derives nothing else. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def bridgelessRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.bridgeless
    { Requires := [K .selection, K .cubicBaseline]
      Produces := [K .bridgeless]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .bridgeless)
        ⟨Contracts.Spine.bridgeless_of_selection BranchState Presentation presentation
          data.toParameters inputs.current.object inputs.current.baseline
          (Nat.le_of_eq (inputs.get (K .cubicBaseline)).down.1.symm)
          (inputs.get (K .selection)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
