import Hypostructure.Graph.WindowCurvatureAlgebra
import Hypostructure.Graph.TypeBMarkedFan

/-!
# The window curvature algebra, identified with its Type B copy

**Legacy boundary.**  `Graph/WindowCurvatureAlgebra.lean` states the label
algebra of `lem:labels` at a parameterised window order.  `Graph.TypeBMarkedFan`
holds the order-fixed copy of the same notions, and these theorems identify the
two.

The identification is real mathematics, but `TypeBMarkedFan` sits on the legacy
`Core.Residual.Ledger` stack, so importing it from the algebra would drag that
stack into the entry spine's node `[18]`.  Keeping the bridge here lets the
spine consume `Labels`, `Legal`, and `curvatureTwo` on their own.
-/

namespace Hypostructure.Graph.WindowCurvature

open Hypostructure.Graph

/-! ## Identification with the Type B copy of the same algebra -/

/-- The coordinate distance of this file is the Type B `gap`.

*Provenance.* Consumes `Graph.TypeBMarkedFan.gap` at
`Graph/TypeBMarkedFan.lean:72`; the `Nat.dist` spelling follows
`Graph.InducedPathCold.offsetDistance` at `Graph/InducedPathCold.lean:1066`.
-/
theorem dist_eq_gap (i j : TypeBMarkedFan.Index) :
    Nat.dist i.1 j.1 = TypeBMarkedFan.gap i j := by
  unfold Nat.dist TypeBMarkedFan.gap
  omega

/-- The cycle this file closes through the path is the Type B outside cycle.

*Provenance.* Consumes `Graph.TypeBMarkedFan.outsideCycleLength` at
`Graph/TypeBMarkedFan.lean:117`.
-/
theorem closingLength_eq_outsideCycleLength (shift : Nat)
    (i j : TypeBMarkedFan.Index) :
    closingLength shift (Nat.dist i.1 j.1) =
      TypeBMarkedFan.outsideCycleLength shift i j := by
  rw [closingLength, TypeBMarkedFan.outsideCycleLength, dist_eq_gap]

/-- The registered dyadic target and the Type B `IsDyadic` accept the same
closing cycles as soon as the outside path is nonempty.  They differ only on
the length `2`, i.e. only at outside length `0` on a coincident pair.

*Provenance.* Consumes `Core.DyadicLength.powerOfTwoLength_iff` at
`Core/DyadicLength.lean:40` and `Graph.TypeBMarkedFan.IsDyadic` at
`Graph/TypeBMarkedFan.lean:69`.
-/
theorem forbiddenGap_iff_isDyadic {shift : Nat} (positive : 0 < shift)
    (i j : TypeBMarkedFan.Index) :
    ForbiddenGap shift (Nat.dist i.1 j.1) ↔
      TypeBMarkedFan.IsDyadic (TypeBMarkedFan.outsideCycleLength shift i j) := by
  rw [ForbiddenGap, closingLength_eq_outsideCycleLength, powerOfTwoLength_iff]
  constructor
  · rintro ⟨exponent, _, equation⟩
    exact ⟨exponent, equation⟩
  · rintro ⟨exponent, equation⟩
    refine ⟨exponent, ?_, equation⟩
    by_contra small
    have le_one : exponent ≤ 1 := by omega
    have bound : (2 : Nat) ^ exponent ≤ 2 := by
      calc (2 : Nat) ^ exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) le_one
        _ = 2 := rfl
    rw [TypeBMarkedFan.outsideCycleLength] at equation
    omega

/-- The safety relation of this file at the registered order *is*
`Graph.TypeBMarkedFan.SafeAtDistance`, on every nonempty outside length.

*Provenance.* Consumes `Graph.TypeBMarkedFan.SafeAtDistance` at
`Graph/TypeBMarkedFan.lean:175`.
-/
theorem safe_iff_safeAtDistance {shift : Nat} (positive : 0 < shift)
    (source target : Label windowOrder) :
    Safe shift source target ↔
      TypeBMarkedFan.SafeAtDistance shift source target := by
  constructor
  · intro safe i memI j memJ dyadic
    exact safe i memI j memJ ((forbiddenGap_iff_isDyadic positive i j).mpr dyadic)
  · intro safe i memI j memJ forbidden
    exact safe i memI j memJ ((forbiddenGap_iff_isDyadic positive i j).mp forbidden)

/-- Legality of this file at the registered order *is* Type B legality
together with nonemptiness, which is the manuscript's own scoping ("a nonempty
label `S` is legal if …").

*Provenance.* Consumes `Graph.TypeBMarkedFan.IsLegal` at
`Graph/TypeBMarkedFan.lean:122`.
-/
theorem legal_iff_isLegal (label : Label windowOrder) :
    Legal label ↔ label.Nonempty ∧ TypeBMarkedFan.IsLegal label := by
  rw [legal_iff_dist, TypeBMarkedFan.IsLegal]
  constructor
  · rintro ⟨nonempty, distinct⟩
    refine ⟨nonempty, fun i memI j memJ => ?_⟩
    obtain ⟨left, right⟩ := distinct i memI j memJ
    rw [← dist_eq_gap]
    exact ⟨left, right⟩
  · rintro ⟨nonempty, distinct⟩
    refine ⟨nonempty, fun i memI j memJ => ?_⟩
    obtain ⟨left, right⟩ := distinct i memI j memJ
    rw [dist_eq_gap]
    exact ⟨left, right⟩

/-- The two-step curvature tensor's unsafe factor is the Type B wedge relation:
`1 - C₂(S,T)` is exactly the failure of `WedgeSafe`.

*Provenance.* Consumes `Graph.TypeBMarkedFan.WedgeSafe` at
`Graph/TypeBMarkedFan.lean:180`.
-/
theorem safe_two_iff_wedgeSafe (source target : Label windowOrder) :
    Safe 2 source target ↔ TypeBMarkedFan.WedgeSafe source target :=
  safe_iff_safeAtDistance (by decide) source target

end Hypostructure.Graph.WindowCurvature
