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

/-! ## Node `[72]`: compatible-pair positive Type-B routing -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def compatiblePairTypeBRoutingRow :
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
    `Hypostructure.Graph.Strategy.Spine.compatiblePairTypeBRouting
    { Requires := [K .compatiblePairFanClosure,
        K .fanClosedPortTypeBRouting]
      Produces := [K .compatiblePairTypeBRouting]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let pairClosure := (inputs.get (K .compatiblePairFanClosure)).down
      let fanClosedRouting :=
        (inputs.get (K .fanClosedPortTypeBRouting)).down
      .cons (key := K .compatiblePairTypeBRouting) ⟨by
        classical
        change CompatiblePairTypeBRoutingStatement data inputs.current.object
        intro profile ledger normal scale left right compatible leftRemainder
          rightRemainder leftAssigned rightAssigned
        obtain ⟨leftClosed, rightClosed, distinct⟩ :=
          pairClosure profile left right compatible leftRemainder rightRemainder
            leftAssigned rightAssigned
        have pairCard : ({left, right} : Finset inputs.current.object.Vertex).card = 2 :=
          Finset.card_pair distinct
        have fanClosed : ∀ vertex ∈
            ({left, right} : Finset inputs.current.object.Vertex),
            profile.IsFanClosed vertex := by
          intro vertex member
          rcases Finset.mem_insert.1 member with rfl | member
          · exact leftClosed
          · rw [Finset.mem_singleton] at member
            subst member
            exact rightClosed
        have routed := fanClosedRouting profile ledger normal scale
          ({left, right} : Finset inputs.current.object.Vertex) fanClosed
          (by rw [pairCard])
        have canonical := Graph.TypeBFanClosedPorts.compatiblePairTypeBRouting
          profile ledger normal scale compatible leftRemainder rightRemainder
            leftAssigned rightAssigned
        rw [pairCard] at routed
        exact ⟨routed.1, canonical.2⟩
      ⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
