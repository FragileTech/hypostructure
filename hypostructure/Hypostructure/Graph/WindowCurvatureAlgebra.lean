import Mathlib.Data.Nat.Dist
import Hypostructure.Core.DyadicLength
import Hypostructure.Graph.External.HegdeSandeepShashank

/-!
# The `P₁₃` curvature algebra

This file is the framework translation of the section *The `P₁₃` curvature
algebra* of `original_erdos_64_proof.tex`, together with `lem:labels` (whose
enumeration is in `Graph/WindowCurvatureEnumeration.lean`).

Let `P = v₀v₁⋯v_{order-1}` be an induced path.  The manuscript reads:

> A nonempty label `S` is *legal* if a single outside vertex `x` with
> attachment label `S` forms no power-of-two cycle together with `P`.  Indeed,
> if `x` is adjacent to `vᵢ` and `vⱼ` with `i < j`, then the subpath
> `vᵢ ⋯ vⱼ`, which has length `j - i`, together with the two edges `x vᵢ` and
> `x vⱼ` forms a cycle of length `(j - i) + 2`.

and, for `s ≥ 0`,

> `C_s(S,T) = 1` if and only if `s + 2 + |i - j| ∉ Pow` for all `i ∈ S`,
> `j ∈ T`.

Everything below is that text and nothing else.  In particular:

* the *forbidden differences* are never written down as a set.  They are the
  differences `d` for which the closing cycle length `s + 2 + d` is accepted by
  the registered dyadic target `Core.DyadicLength.PowerOfTwoLength`.  The
  manuscript's own `{2, 6}` at `s = 0` is recovered as the theorem
  `forbiddenGaps_zero` at the registered induced-path order, not assumed;
* the path order is a parameter.  The registered `13` enters only through
  `Graph.External.HegdeSandeepShashank.inducedPathOrder` at the specialization
  lemmas, never as a literal in a definition.

## Relation to what is already in the framework

The `13`-fixed Type B copy of this algebra already exists as
`Graph.TypeBMarkedFan.gap`, `IsLegal`, `SafeAtDistance` and `WedgeSafe`.  It is
*not* redefined here: `safe_iff_safeAtDistance`, `legal_iff_isLegal` and
`safe_two_iff_wedgeSafe` identify the two, so the order-generic algebra of this
file and the Type B algebra are one object seen at two orders.

## What is stated here and what is retrieved

Stated (the manuscript's own mathematics, and only it): `Label`, `Safe` (`C_s`),
`Legal`, `Labels`, `curvatureTwo` (`Ω₂`).

Retrieved, never restated:

* the accepted cycle lengths -- `Core.DyadicLength.PowerOfTwoLength` at
  `Core/DyadicLength.lean:21` and `powerOfTwoLength_iff` at
  `Core/DyadicLength.lean:40`;
* the registered path order -- `Graph.External.HegdeSandeepShashank.inducedPathOrder`
  at `Graph/External/HegdeSandeepShashank.lean:18`;
* the order-`13`-fixed copy of this very algebra --
  `Graph.TypeBMarkedFan.gap`, `IsLegal`, `SafeAtDistance`, `WedgeSafe` at
  `Graph/TypeBMarkedFan.lean:72,122,175,180`, identified with this one below.

Every declaration below carries its own `*Provenance.*` line.
-/

namespace Hypostructure.Graph.WindowCurvature

open Hypostructure.Core.DyadicLength

/-- The set of path coordinates an outside vertex attaches to.  The manuscript's
`S(x) ⊆ {0, …, order-1}`.

*Provenance.* Follows `Graph.TypeBMarkedFan.Label` at
`Graph/TypeBMarkedFan.lean:155`, the order-`13`-fixed copy of this carrier.
-/
abbrev Label (order : Nat) : Type := Finset (Fin order)

/-! ## The forbidden differences, derived -/

/-- The cycle closed through the induced path by an outside path of length
`shift` between coordinates at distance `difference`: the `difference` edges of
the subpath, the `shift` outside edges, and the two attachment edges.  This is
the manuscript's `s + 2 + |i - j|`.

*Provenance.* Follows `Graph.TypeBMarkedFan.outsideCycleLength` at
`Graph/TypeBMarkedFan.lean:117`.
-/
def closingLength (shift difference : Nat) : Nat := shift + 2 + difference

/-- A coordinate difference is *forbidden at `shift`* when the cycle it closes
is accepted by the registered dyadic target.  This is the only place a
forbidden difference is ever named, and it names none: it asks the target.

*Provenance.* Consumes `Core.DyadicLength.PowerOfTwoLength` at
`Core/DyadicLength.lean:21`.
-/
def ForbiddenGap (shift difference : Nat) : Prop :=
  PowerOfTwoLength (closingLength shift difference)

/-- *Provenance.* Consumes `Core.DyadicLength.powerOfTwoLengthDecidable` at
`Core/DyadicLength.lean:25`. -/
instance forbiddenGapDecidable (shift difference : Nat) :
    Decidable (ForbiddenGap shift difference) :=
  inferInstanceAs (Decidable (PowerOfTwoLength _))

/-- The forbidden differences available inside a path of the given order.  A
finite set, derived from the target, never listed.

*Provenance.* Follows `Graph.TypeBMarkedFan.compatibleParts` at
`Graph/TypeBMarkedFan.lean:338`, a `Finset.filter` of a derived arithmetic
condition.
-/
def forbiddenGaps (order shift : Nat) : Finset Nat :=
  (Finset.range order).filter (ForbiddenGap shift)

/-- *Provenance.* Follows `Graph.TypeBMarkedFan.wedgeSafe_iff` at
`Graph/TypeBMarkedFan.lean:196`. -/
theorem mem_forbiddenGaps {order shift difference : Nat} :
    difference ∈ forbiddenGaps order shift ↔
      difference < order ∧ ForbiddenGap shift difference := by
  simp [forbiddenGaps, Finset.mem_filter, Finset.mem_range]

/-- Two coordinates of a path of the given order are closer than its order.

*Provenance.* Follows `Graph.TypeBMarkedFan.gap_le_twelve` at
`Graph/TypeBMarkedFan.lean:80`.
-/
theorem dist_lt_order {order : Nat} (i j : Fin order) :
    Nat.dist i.1 j.1 < order := by
  have hi := i.2
  have hj := j.2
  unfold Nat.dist
  omega

/-! ## The safety relation `C_s` -/

/-- The manuscript's safety relation: `C_shift(source, target) = 1` iff
`shift + 2 + |i - j| ∉ Pow` for all `i ∈ source`, `j ∈ target`.  An outside
path of length `shift` between vertices carrying these labels is safe through
the induced path exactly when this holds.

*Provenance.* Follows `Graph.TypeBMarkedFan.SafeAtDistance` at
`Graph/TypeBMarkedFan.lean:175`.
-/
def Safe {order : Nat} (shift : Nat) (source target : Label order) : Prop :=
  ∀ i ∈ source, ∀ j ∈ target, ¬ ForbiddenGap shift (Nat.dist i.1 j.1)

/-- Safety read against the derived forbidden-difference set.  This is the form
the decision procedure uses: the target is asked once per admissible
difference rather than once per pair of coordinates.

*Provenance.* Follows `Graph.TypeBMarkedFan.wedgeSafe_iff` at
`Graph/TypeBMarkedFan.lean:196`.
-/
theorem safe_iff_notMem_forbiddenGaps {order : Nat} (shift : Nat)
    (source target : Label order) :
    Safe shift source target ↔
      ∀ i ∈ source, ∀ j ∈ target,
        Nat.dist i.1 j.1 ∉ forbiddenGaps order shift := by
  constructor
  · intro safe i memI j memJ member
    exact safe i memI j memJ (mem_forbiddenGaps.mp member).2
  · intro safe i memI j memJ forbidden
    exact safe i memI j memJ
      (mem_forbiddenGaps.mpr ⟨dist_lt_order i j, forbidden⟩)

/-- *Provenance.* Follows `Core.DyadicLength.powerOfTwoLengthDecidable` at
`Core/DyadicLength.lean:25`; consumes `safe_iff_notMem_forbiddenGaps` above. -/
instance safeDecidable {order : Nat} (shift : Nat) (source target : Label order) :
    Decidable (Safe shift source target) :=
  decidable_of_iff _ (safe_iff_notMem_forbiddenGaps shift source target).symm

/-- *Provenance.* Follows `Graph.TypeBMarkedFan.wedgeSafe_comm` at
`Graph/TypeBMarkedFan.lean:222`. -/
theorem safe_comm {order : Nat} {shift : Nat} {source target : Label order}
    (safe : Safe shift source target) : Safe shift target source := by
  intro i memI j memJ forbidden
  exact safe j memJ i memI (by rwa [Nat.dist_comm])

/-! ## Legal labels -/

/-- A nonempty label is legal exactly when a single outside vertex carrying it
closes no accepted cycle through the path: the manuscript's legality is the
safety relation at outside length zero, applied to the label against itself.

*Provenance.* Follows `Graph.TypeBMarkedFan.IsLegal` at
`Graph/TypeBMarkedFan.lean:122`.
-/
def Legal {order : Nat} (label : Label order) : Prop :=
  label.Nonempty ∧ Safe 0 label label

/-- *Provenance.* Follows `Core.DyadicLength.powerOfTwoLengthDecidable` at
`Core/DyadicLength.lean:25`. -/
instance legalDecidable {order : Nat} (label : Label order) :
    Decidable (Legal label) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `Labels`: the legal nonempty labels of a path of the given order.

*Provenance.* Follows `Graph.TypeBMarkedFan.compatibleParts` at
`Graph/TypeBMarkedFan.lean:338`.
-/
def Labels (order : Nat) : Finset (Label order) :=
  Finset.univ.filter Legal

/-- *Provenance.* Follows `Graph.TypeBMarkedFan.wedgeSafe_iff` at
`Graph/TypeBMarkedFan.lean:196`. -/
theorem mem_Labels {order : Nat} {label : Label order} :
    label ∈ Labels order ↔ Legal label := by
  simp [Labels, Finset.mem_filter]

/-! ## The two-step curvature tensor -/

/-- `Ω₂(S, A, T) = C₁(S,A) · C₁(A,T) · (1 - C₂(S,T))`: two individually safe
outside edges composing into an unsafe outside path of length two.

*Provenance.* Follows `Graph.TypeBMarkedFan.WedgeSafe` at
`Graph/TypeBMarkedFan.lean:180`, which is its third factor.
-/
def curvatureTwo {order : Nat} (source middle target : Label order) : Bool :=
  decide (Safe 1 source middle) && decide (Safe 1 middle target) &&
    !decide (Safe 2 source target)

/-- *Provenance.* Follows `Graph.TypeBMarkedFan.wedgeSafe_iff` at
`Graph/TypeBMarkedFan.lean:196`. -/
theorem curvatureTwo_eq_true_iff {order : Nat}
    (source middle target : Label order) :
    curvatureTwo source middle target = true ↔
      Safe 1 source middle ∧ Safe 1 middle target ∧ ¬ Safe 2 source target := by
  simp [curvatureTwo, and_assoc]

/-! ## The registered induced-path order

Below this line the order is the one the external theorem is registered at.
It is read, never written. -/

/-- The order of the induced windows the spine packs: the induced-path order of
the registered external theorem.

*Provenance.* Consumes `Graph.External.HegdeSandeepShashank.inducedPathOrder`
at `Graph/External/HegdeSandeepShashank.lean:18`.
-/
abbrev windowOrder : Nat := External.HegdeSandeepShashank.inducedPathOrder

/-- **The manuscript's own forbidden differences, derived.**  At outside length
zero and the registered window order, the differences whose closing cycle is
accepted are exactly `2` and `6` -- `(j - i) + 2 ∈ {4, 8}` -- which is the
sentence the manuscript proves before it defines `Labels`.  Nothing here is
listed in a definition; the numerals appear only in this conclusion.

*Provenance.* Consumes `Core.DyadicLength.powerOfTwoLengthDecidable` at
`Core/DyadicLength.lean:25` and `windowOrder`; the same two numerals appear as
`Graph.TypeBMarkedFan.isDyadic_attachmentCycleLength_iff` at
`Graph/TypeBMarkedFan.lean:127`, which this derives rather than repeats.
-/
theorem forbiddenGaps_zero : forbiddenGaps windowOrder 0 = {2, 6} := by
  decide

/-- The forbidden differences at outside length one: `(j - i) + 3 ∈ {4, 8}`.

*Provenance.* Consumes `Core.DyadicLength.powerOfTwoLengthDecidable` at
`Core/DyadicLength.lean:25` and `windowOrder`.
-/
theorem forbiddenGaps_one : forbiddenGaps windowOrder 1 = {1, 5} := by
  decide

/-- The forbidden differences at outside length two, i.e. the wedge gaps
`{0, 4, 12}` of `Graph.TypeBMarkedFan.isDyadic_wedgeCycle_iff`.

*Provenance.* Consumes `Core.DyadicLength.powerOfTwoLengthDecidable` at
`Core/DyadicLength.lean:25`; the same three numerals appear as
`Graph.TypeBMarkedFan.isDyadic_wedgeCycle_iff` at
`Graph/TypeBMarkedFan.lean:185`.
-/
theorem forbiddenGaps_two : forbiddenGaps windowOrder 2 = {0, 4, 12} := by
  decide

/-- Legality in the manuscript's stated form: `|i - j| ∉ {2, 6}`.

*Provenance.* Consumes `forbiddenGaps_zero` above; follows
`Graph.TypeBMarkedFan.isLegal_iff_attachment_not_dyadic` at
`Graph/TypeBMarkedFan.lean:137`.
-/
theorem legal_iff_dist {label : Label windowOrder} :
    Legal label ↔ label.Nonempty ∧
      ∀ i ∈ label, ∀ j ∈ label,
        Nat.dist i.1 j.1 ≠ 2 ∧ Nat.dist i.1 j.1 ≠ 6 := by
  rw [Legal, safe_iff_notMem_forbiddenGaps, forbiddenGaps_zero]
  constructor
  · rintro ⟨nonempty, safe⟩
    refine ⟨nonempty, fun i memI j memJ => ⟨fun equal => ?_, fun equal => ?_⟩⟩
    · exact safe i memI j memJ (by simp [equal])
    · exact safe i memI j memJ (by simp [equal])
  · rintro ⟨nonempty, distinct⟩
    refine ⟨nonempty, fun i memI j memJ member => ?_⟩
    obtain ⟨left, right⟩ := distinct i memI j memJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    exact member.elim left right

end Hypostructure.Graph.WindowCurvature
