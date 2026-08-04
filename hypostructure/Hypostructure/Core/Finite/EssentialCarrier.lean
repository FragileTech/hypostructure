import Hypostructure.Core.Finite.Enumeration

/-!
# Finite essential-carrier reduction

Select an inclusion-minimal finite carrier set for any decidable completeness
predicate.  This is domain-neutral: graph response incidences and represented
PDE observables instantiate the same construction.
-/

namespace Hypostructure.Core.Finite.EssentialCarrier

open Hypostructure.Core.Finite

universe u

structure Profile where
  Carrier : Type u
  schedule : Enumeration Carrier
  Complete : Finset Carrier -> Prop
  completeDecidable : (carriers : Finset Carrier) -> Decidable (Complete carriers)
  fullComplete : Complete schedule.toFinset

namespace Profile

variable (profile : Profile)

private def hasCompleteCard (n : Nat) : Prop :=
  ∃ carriers : Finset profile.Carrier,
    profile.Complete carriers ∧ carriers.card = n

private theorem exists_complete_card (profile : Profile) :
    ∃ n, profile.hasCompleteCard n :=
  ⟨profile.schedule.card, profile.schedule.toFinset,
    profile.fullComplete, profile.schedule.card_toFinset⟩

noncomputable def minimumCard (profile : Profile) : Nat := by
  classical
  exact Nat.find (exists_complete_card profile)

private theorem minimumCard_spec (profile : Profile) :
    profile.hasCompleteCard profile.minimumCard :=
  by
    classical
    exact Nat.find_spec (exists_complete_card profile)

noncomputable def core (profile : Profile) : Finset profile.Carrier :=
  Classical.choose profile.minimumCard_spec

theorem core_complete (profile : Profile) : profile.Complete profile.core :=
  (Classical.choose_spec profile.minimumCard_spec).1

theorem core_card (profile : Profile) :
    profile.core.card = profile.minimumCard :=
  (Classical.choose_spec profile.minimumCard_spec).2

theorem minimumCard_le
    (profile : Profile)
    (carriers : Finset profile.Carrier)
    (complete : profile.Complete carriers) :
    profile.minimumCard ≤ carriers.card := by
  classical
  exact Nat.find_min' (exists_complete_card profile)
    ⟨carriers, complete, rfl⟩

/-- Every selected carrier is essential: deleting it destroys completeness. -/
theorem erase_not_complete
    (profile : Profile)
    [DecidableEq profile.Carrier]
    (carrier : profile.Carrier) (mem : carrier ∈ profile.core) :
    ¬ profile.Complete (profile.core.erase carrier) := by
  classical
  intro complete
  have lower := profile.minimumCard_le (profile.core.erase carrier) complete
  rw [← profile.core_card] at lower
  have erasedCard :
      (profile.core.erase carrier).card = profile.core.card - 1 :=
    Finset.card_erase_of_mem mem
  rw [erasedCard] at lower
  have positive : 0 < profile.core.card := Finset.card_pos.mpr ⟨carrier, mem⟩
  omega

end Profile

end Hypostructure.Core.Finite.EssentialCarrier
