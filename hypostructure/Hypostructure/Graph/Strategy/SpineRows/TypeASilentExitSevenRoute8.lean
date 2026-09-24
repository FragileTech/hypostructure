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

omit [FactSystem (Input BranchState Presentation presentation data)] in
/-- Forget only the additional provenance field when the common route-`8`
rows are entered.  The stronger silent-origin fact remains on the ledger. -/
@[reducible] noncomputable def typeASilentExitSevenRoute8Row :
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
    `Hypostructure.Graph.Strategy.Spine.typeASilentExitSevenRoute8
    { Requires := [K .typeASilentExitSevenFree]
      Produces := [K .typeAExitSevenFree]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAExitSevenFree)
        (show Value BranchState Presentation presentation data
            .typeAExitSevenFree inputs.current from ⟨by
          classical
          obtain ⟨packing, canonical, valid, maximal, component, present,
            negative, zero, receiver, isReceiver, peeled, peeledSubset,
            saturated, noExitFour, noExitFive, noExitSix, _origin,
            noHandoff⟩ :=
            (inputs.get (K .typeASilentExitSevenFree)).down
          exact ⟨packing, canonical, valid, maximal, component, present,
            negative, zero, receiver, isReceiver, peeled, peeledSubset,
            saturated, noExitFour, noExitFive, noExitSix, noHandoff⟩⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
