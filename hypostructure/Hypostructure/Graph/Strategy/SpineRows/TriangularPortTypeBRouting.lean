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

/-! ## Nodes `[78]`--`[81]`, feeding `[72]`: triangular-port Type-B routing -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def triangularPortTypeBRoutingRow :
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
    `Hypostructure.Graph.Strategy.Spine.triangularPortTypeBRouting
    { Requires := [K .fanClosedPort, K .fanClosedPortTypeBRouting]
      Produces := [K .triangularPortTypeBRouting]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let fanClosedDefinition := (inputs.get (K .fanClosedPort)).down
      let fanClosedRouting :=
        (inputs.get (K .fanClosedPortTypeBRouting)).down
      .cons (key := K .triangularPortTypeBRouting) ⟨by
        classical
        change TriangularPortTypeBRoutingStatement data inputs.current.object
        intro profile ledger normal scale ports triangular cardPorts degreeFive
          remainder assigned
        have fanClosed : ∀ endpoint ∈ ports,
            profile.IsFanClosed endpoint := by
          intro endpoint member
          have direct : profile.IsFanClosed endpoint :=
            ⟨remainder endpoint member, assigned endpoint member⟩
          exact (fanClosedDefinition profile endpoint).2
            ((fanClosedDefinition profile endpoint).1 direct)
        have two : 2 ≤ ports.card := by omega
        have routed :=
          fanClosedRouting profile ledger normal scale ports fanClosed two
        have canonical := Graph.TypeBFanClosedPorts.triangularPortTypeBRouting
          profile ledger normal scale triangular cardPorts degreeFive remainder
            assigned
        exact ⟨routed.1, canonical.2⟩
      ⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
