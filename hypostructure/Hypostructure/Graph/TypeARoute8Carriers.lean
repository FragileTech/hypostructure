import Hypostructure.Graph.AtomResponse
import Hypostructure.Graph.TypeAReceiverClosure



namespace Hypostructure.Graph.TypeARoute8Carriers

universe u v

open Hypostructure

/-! ## The boundary-incidence carrier is the framework's

`def:typeA-route8-carriers` writes the carrier supply of a Type A support as its
boundary incidences `∂_E X`.  That carrier is **not defined here**: it is
`Official.Features.PackedWindowTokenLedger.boundaryIncidences`, the literal
support-to-complement incidence set, whose cardinality the framework already
identifies with the ledger's own incidence count in `boundary_count_exact`.  The
per-vertex fibre is `SupportIncidenceLedger.outsideNeighbors`.  Rebuilding either
one as a `Finset.sigma` here would be a second copy of a framework carrier. -/




theorem carrierBudgetContradiction
    {discharge required entryCount deficiency supply ambient : Nat}
    (dischargePos : 0 < discharge) (requiredPos : 0 < required)
    (burden : discharge * deficiency ≤ entryCount)
    (deficit : ambient ≤ discharge * deficiency + discharge * supply)
    (budget : required * entryCount ≤ supply)
    (rate : (required * discharge + 1) * supply < required * ambient) :
    False := by
  -- `required · ambient ≤ required · discharge · (deficiency + supply)`
  have scaled : required * ambient ≤
      required * (discharge * deficiency) + required * (discharge * supply) := by
    have step : required * ambient ≤
        required * (discharge * deficiency + discharge * supply) :=
      Nat.mul_le_mul_left _ deficit
    rwa [Nat.mul_add] at step
  -- the burden turns the first summand into the private-carrier budget
  have burdenScaled : required * (discharge * deficiency) ≤
      required * entryCount :=
    Nat.mul_le_mul_left _ burden
  have budgetChain : required * (discharge * deficiency) ≤ supply :=
    le_trans burdenScaled budget
  have collide : required * ambient ≤ supply + required * discharge * supply := by
    have assoc : required * (discharge * supply) = required * discharge * supply :=
      (mul_assoc _ _ _).symm
    rw [assoc] at scaled
    omega
  have expand : (required * discharge + 1) * supply =
      required * discharge * supply + supply := by
    rw [add_mul, one_mul]
  omega


/-- **`lem:typeA-one-terminal-collapse`.**  *"If `α_𝒳(ξ) ≤ 1` then one of exits
(4)--(7) occurs.  Consequently, every indexed entry in a true route-8 residual
satisfies `α_𝒳(ξ) ≥ 2`."*  This is the second sentence; `collapse` is the
first, and the four absences are `def:typeA-true-route8-residual`. -/
theorem two_le_alpha_of_trueRouteEight
    {ExitFour ExitFive ExitSix ExitSeven : Prop} {alpha : Nat}
    (collapse : alpha ≤ 1 → ExitFour ∨ ExitFive ∨ ExitSix ∨ ExitSeven)
    (noFour : ¬ ExitFour) (noFive : ¬ ExitFive)
    (noSix : ¬ ExitSix) (noSeven : ¬ ExitSeven) :
    2 ≤ alpha := by
  by_contra small
  rcases collapse (by omega) with four | five | six | seven
  · exact noFour four
  · exact noFive five
  · exact noSix six
  · exact noSeven seven


theorem no_terminalTwoCarrier {Carrier : Type u} {ExitFour : Prop}
    {essential : Finset Carrier}
    (coreNontrivial : 2 ≤ essential.card)
    (deletionExit : ∀ carrier ∈ essential, ExitFour)
    (trueResidual : ¬ ExitFour) :
    False := by
  obtain ⟨carrier, member⟩ := Finset.card_pos.mp (by omega : 0 < essential.card)
  exact trueResidual (deletionExit carrier member)

end Hypostructure.Graph.TypeARoute8Carriers
