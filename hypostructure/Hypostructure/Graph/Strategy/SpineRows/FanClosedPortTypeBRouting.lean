import Hypostructure.Graph.Strategy.SpineVocabulary

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

/-! ## Node `[72]`: fan-closed ports enter the positive Type-B ledger -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def fanClosedPortTypeBRoutingRow :
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
    `Hypostructure.Graph.Strategy.Spine.fanClosedPortTypeBRouting
    { Requires := [K .fanClosedPort]
      Produces := [K .fanClosedPortTypeBRouting]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let fanClosedDefinition := (inputs.get (K .fanClosedPort)).down
      .cons (key := K .fanClosedPortTypeBRouting) ⟨by
        change FanClosedPortTypeBRoutingStatement data inputs.current.object
        intro profile ledger normal scale ports fanClosed two
        apply Graph.TypeBFanClosedPorts.fanClosedPortTypeBRouting
          profile ledger normal scale
        · intro vertex member
          exact (fanClosedDefinition profile vertex).2
            ((fanClosedDefinition profile vertex).1 (fanClosed vertex member))
        · exact two
      ⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
