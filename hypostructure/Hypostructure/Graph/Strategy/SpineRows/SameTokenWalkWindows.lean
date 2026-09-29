import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SameTokenWalkWindows

/-!
# Induced windows along the canonical port walks; exchange at `P₀`
(`[144a]` exchange attack, Lean improvement)

One Type A row (contracts: `Graph/Contracts/Spine/SameTokenWalkWindows.lean`).  No row decides
or splits anything.  Right after `K .sameTokenPatternSupports` (node `[144]`, above the handoff
decision), the earliest position: the contract reads only the canonical routing's existence
(`K .sameTokenPatternSupports`), the cycle avoidance (`K .selection`), the active surplus family
(`K .activeSurplusFamily`) and `δ = 3` (`K .cubicBaseline`), so every `[144a]` ledger carries
the two facts.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[144]`, after the pattern supports: the induced windows along the canonical port
walks (9850) and the exchange at G's canonical packing `P₀` (9851). -/
@[reducible] noncomputable def sameTokenWalkWindowsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sameTokenWalkWindows
    { Requires := [K .sameTokenPatternSupports, K .selection, K .activeSurplusFamily,
        K .cubicBaseline]
      Produces := [K .sameTokenWalkWindows, K .sameTokenWalkExchange]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .sameTokenWalkWindows)
        ⟨Contracts.Spine.SameTokenWalkWindows.sameTokenWalkWindows_holds
          (inputs.get (K .sameTokenPatternSupports)).down
          (inputs.get (K .selection)).down.1
          (inputs.get (K .activeSurplusFamily)).down
          (inputs.get (K .cubicBaseline)).down.1.1⟩
      (.cons (key := K .sameTokenWalkExchange)
        ⟨Contracts.Spine.SameTokenWalkWindows.sameTokenWalkExchange_holds
          (data := data.toParameters) (object := inputs.current.object)⟩
      .nil))

end Hypostructure.Graph.Strategy.Spine
