import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Order.Interval.Finset.Nat

/-!
# Window attachment signatures

`def:typeA-window-attachment-shadow`, generically: for a corridor length `s`
and a window of `order` labelled positions, the *forbidden distance set*
`D_s = {d < order : s + 2 + d is an accepted length}` and the `s`-*signature*
`Sh_s(a) = {b < order : |a − b| ∈ D_s}` of an attachment index `a`.  A
recorded corridor of length `s` between attachments `a` and `b` with
`b ∈ Sh_s(a)` closes an accepted cycle of length `s + 2 + |a − b|`
(`fig:exit4-p13-attachment-accounting`); the singleton table
`lem:typeA-singleton-shadow-table` is instance arithmetic of the registered
presentation and is not restated here.

Everything is parameterized by the accepted-length predicate; no presentation
constant appears.
-/

namespace Hypostructure.Graph.WindowAttachmentShadow

/-- `D_s`: the distances `d < order` whose corridor-closed cycle length
`s + 2 + d` is accepted. -/
noncomputable def forbiddenDistances (LengthOK : Nat → Prop) (order s : Nat) :
    Finset Nat := by
  classical
  exact (Finset.range order).filter fun d => LengthOK (s + 2 + d)

theorem mem_forbiddenDistances {LengthOK : Nat → Prop} {order s d : Nat} :
    d ∈ forbiddenDistances LengthOK order s ↔
      d < order ∧ LengthOK (s + 2 + d) := by
  classical
  simp [forbiddenDistances]

/-- `Sh_s(a)`: the attachment indices whose distance to `a` is forbidden. -/
noncomputable def shadow (LengthOK : Nat → Prop) (order s a : Nat) :
    Finset Nat := by
  classical
  exact (Finset.range order).filter fun b =>
    Nat.dist a b ∈ forbiddenDistances LengthOK order s

theorem mem_shadow {LengthOK : Nat → Prop} {order s a b : Nat} :
    b ∈ shadow LengthOK order s a ↔
      b < order ∧ Nat.dist a b < order ∧ LengthOK (s + 2 + Nat.dist a b) := by
  classical
  simp [shadow, mem_forbiddenDistances]

/-- The signature is symmetric in its two attachments. -/
theorem mem_shadow_symm {LengthOK : Nat → Prop} {order s a b : Nat}
    (aBound : a < order) (member : b ∈ shadow LengthOK order s a) :
    a ∈ shadow LengthOK order s b := by
  classical
  obtain ⟨_bBound, distBound, accepted⟩ := mem_shadow.mp member
  exact mem_shadow.mpr ⟨aBound, by rwa [Nat.dist_comm],
    by rwa [Nat.dist_comm]⟩

/-- A recorded corridor hit closes an accepted cycle length: the length
`s + 2 + |a − b|` of the corridor, its two window-attachment edges, and the
window subpath between the attachments. -/
theorem accepted_of_mem_shadow {LengthOK : Nat → Prop} {order s a b : Nat}
    (member : b ∈ shadow LengthOK order s a) :
    LengthOK (s + 2 + Nat.dist a b) :=
  (mem_shadow.mp member).2.2

/-- **`lem:typeA-singleton-shadow-table`, the tail bound**: when the accepted
lengths meet the corridor's window range `[s + 2, s + 2 + order − 1]` at most
once — the manuscript's `s ≥ 18`, where consecutive powers of two differ by
more than the window order — the forbidden distance set is at most a
singleton.  The exact table for small `s` is instance arithmetic of the
registered presentation (`D_s = {2^q − s − 2 : 0 ≤ 2^q − s − 2 < order}` is
`mem_forbiddenDistances` unfolded) and is not restated here. -/
theorem card_forbiddenDistances_le_one {LengthOK : Nat → Prop}
    {order s : Nat}
    (gap : ∀ d1 < order, ∀ d2 < order,
      LengthOK (s + 2 + d1) → LengthOK (s + 2 + d2) → d1 = d2) :
    (forbiddenDistances LengthOK order s).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr fun d1 mem1 d2 mem2 => ?_
  obtain ⟨bound1, ok1⟩ := mem_forbiddenDistances.mp mem1
  obtain ⟨bound2, ok2⟩ := mem_forbiddenDistances.mp mem2
  exact gap d1 bound1 d2 bound2 ok1 ok2

end Hypostructure.Graph.WindowAttachmentShadow
