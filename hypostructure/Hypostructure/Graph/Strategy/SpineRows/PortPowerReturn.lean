import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Support

/-! # Power-of-two port returns

Every eligible completion port of every receiver of the saturated Type A
support carries an anchored return of power-of-two length, read off the edge
contraction of the port.  The manuscript has no such corollary and no label
for it.  Thin adapter of `Contracts.TypeA.portPowerReturn`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

@[reducible] noncomputable def portPowerReturnRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.portPowerReturn
    { Requires := [K .contractionCritical, K .typeASaturatedReceiver]
      Produces := [K .portPowerReturn]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .portPowerReturn)
        ⟨Graph.Contracts.TypeA.portPowerReturn data.toParameters
          inputs.current.object (inputs.get (K .contractionCritical)).down
          (inputs.get (K .typeASaturatedReceiver)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
