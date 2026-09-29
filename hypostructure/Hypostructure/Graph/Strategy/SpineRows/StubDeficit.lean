import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.StubDeficit

/-!
# `[54]`: the stub-deficit identity and the cycle spectrum of `R₀`

One Type A row, run on the residual arm of `[54]` (after the joint realization
inequality fails), publishing at G's canonical packing `P₀` and remainder `R₀`:
`K .stubDeficitIdentity` (the incidence identity, the handshake for `e(G[R₀])`
and the canonical assignment of deficit units to boundary stubs) and
`K .remainderCycleSpectrum` (`G[R₀]` has no cycle of an accepted length).
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

@[reducible] noncomputable def stubDeficitRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.stubDeficit
    { Requires := [K .selection]
      Produces := [K .stubDeficitIdentity, K .remainderCycleSpectrum]
      requiresUnique := by simp
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .stubDeficitIdentity)
        ⟨Contracts.Spine.stubDeficitIdentity_holds (data := data.toParameters)
          (object := inputs.current.object)⟩
      (.cons (key := K .remainderCycleSpectrum)
        ⟨Contracts.Spine.remainderCycleSpectrum_holds (data := data.toParameters)
          (object := inputs.current.object) (inputs.get (K .selection)).down.1⟩
      .nil))

end Hypostructure.Graph.Strategy.Spine
