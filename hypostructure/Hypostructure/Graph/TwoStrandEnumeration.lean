import Hypostructure.Graph.WindowCurvatureAlgebra

/-!
# The two-strand finite check of the neutral equal-length terminal germ

Node `[163]` of the dense-packing residual is the *neutral equal-length
terminal germ*: two same-interface strands `Q`, `E` of equal length between two
attachment coordinates of a packed window, indistinguishable by every context.
When `E` is a genuine second strand of the graph, the configuration is a
symmetric strand pair: two internally disjoint outside strands of the same
length `ℓ` (counted in edges, stubs included) between the window coordinates at
distance `d`.  Its bounded support closes exactly the cycles

* strand + window segment: `ℓ + d` (each strand), and
* strand + strand: `2ℓ`.

The manuscript's target accepts a closing length exactly when it is a power of
two (`Core.DyadicLength.PowerOfTwoLength`), so a symmetric strand pair is
*dyadically closed* — refuted at a counterexample by the target predicate,
which is node `[155]`/(F1) — precisely when one of those two lengths is a power
of two.  This module is that finite check, stated for every window order and
strand bound and computed by kernel reduction at the manuscript's order.

Nothing here names a numeral of the strategy: the order and the strand bound
are parameters, the target is the registered dyadic length, and the closing
lengths are `Graph.WindowCurvature.closingLength` read at the strand.
-/

namespace Hypostructure.Graph.TwoStrand

open Hypostructure.Core.DyadicLength

/-- A symmetric two-strand configuration at a window: two same-interface
strands of common length `length` (edges, both stubs included) between window
coordinates at distance `gap`. -/
structure Configuration where
  /-- The common strand length, in edges, stubs included. -/
  length : Nat
  /-- The coordinate distance `|a − b|` of the two attachment offsets. -/
  gap : Nat
  deriving DecidableEq, Repr

namespace Configuration

/-- The strand-plus-segment closing length `ℓ + d`. -/
def segmentClosing (config : Configuration) : Nat := config.length + config.gap

/-- The strand-plus-strand closing length `2ℓ`. -/
def pairClosing (config : Configuration) : Nat := 2 * config.length

/-- The configuration is dyadically closed: one of its two closing lengths is
accepted by the target. -/
def DyadicallyClosed (config : Configuration) : Prop :=
  PowerOfTwoLength config.segmentClosing ∨ PowerOfTwoLength config.pairClosing

instance (config : Configuration) : Decidable config.DyadicallyClosed :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A configuration *survives* the finite check when neither closing length is
accepted. -/
def Survives (config : Configuration) : Prop := ¬ config.DyadicallyClosed

instance (config : Configuration) : Decidable config.Survives :=
  inferInstanceAs (Decidable (¬ _))

end Configuration

/-- The strand length equals `closingLength shift 0` for the outside shift
`shift = length − 2` when the strand has both stubs: the strand is an outside
path of `shift` edges plus the two attachment edges, exactly the manuscript's
`s + 2`. -/
theorem length_eq_closingLength (shift : Nat) :
    WindowCurvature.closingLength shift 0 = shift + 2 := by
  simp [WindowCurvature.closingLength]

/-- The strand-plus-segment closing length is the manuscript's `s + 2 + |i−j|`
of the label algebra at the strand's outside shift. -/
theorem segmentClosing_eq_closingLength (shift gap : Nat) :
    (Configuration.mk (shift + 2) gap).segmentClosing =
      WindowCurvature.closingLength shift gap := by
  simp only [Configuration.segmentClosing, WindowCurvature.closingLength]

/-- **The symmetric-pair criterion.**  A symmetric strand pair whose common
length is itself an accepted dyadic length is dyadically closed by the pair
cycle `2ℓ`. -/
theorem dyadicallyClosed_of_powerOfTwo_length (config : Configuration)
    (dyadic : PowerOfTwoLength config.length) : config.DyadicallyClosed := by
  right
  obtain ⟨exponent, lower, equality⟩ := (powerOfTwoLength_iff _).1 dyadic
  refine (powerOfTwoLength_iff _).2 ⟨exponent + 1, by omega, ?_⟩
  simp [Configuration.pairClosing, equality, pow_succ]
  ring

/-- **The segment criterion.**  A strand pair whose strand-plus-segment length
is accepted is dyadically closed by that cycle: this is case (F1) of
`def:cold-corridor-first-failure` read at the strand. -/
theorem dyadicallyClosed_of_powerOfTwo_segment (config : Configuration)
    (dyadic : PowerOfTwoLength config.segmentClosing) : config.DyadicallyClosed :=
  Or.inl dyadic

/-! ## The finite check at a window order and strand bound -/

/-- All configurations with strand length at most `bound` and gap below the
window order. -/
def configurations (order bound : Nat) : List Configuration :=
  (List.range (bound + 1)).flatMap fun length =>
    (List.range order).map fun gap => ⟨length, gap⟩

/-- The configurations the finite check does not close. -/
def survivors (order bound : Nat) : List Configuration :=
  (configurations order bound).filter fun config => decide config.Survives

theorem mem_configurations {order bound : Nat} {config : Configuration} :
    config ∈ configurations order bound ↔
      config.length ≤ bound ∧ config.gap < order := by
  simp only [configurations, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨length, lengthLt, gap, gapLt, rfl⟩
    exact ⟨Nat.lt_succ_iff.mp lengthLt, gapLt⟩
  · rintro ⟨lengthLe, gapLt⟩
    exact ⟨config.length, by omega, config.gap, gapLt, rfl⟩

theorem mem_survivors {order bound : Nat} {config : Configuration} :
    config ∈ survivors order bound ↔
      config.length ≤ bound ∧ config.gap < order ∧ config.Survives := by
  simp only [survivors, List.mem_filter, mem_configurations, decide_eq_true_eq]
  tauto

/-- The finite check closes every configuration at the given order and bound
exactly when the survivor list is empty. -/
theorem survivors_eq_nil_iff (order bound : Nat) :
    survivors order bound = [] ↔
      ∀ config : Configuration,
        config.length ≤ bound → config.gap < order → config.DyadicallyClosed := by
  constructor
  · intro empty config lengthLe gapLt
    by_contra survives
    have := mem_survivors.2 ⟨lengthLe, gapLt, survives⟩
    rw [empty] at this
    exact List.not_mem_nil this
  · intro closed
    rw [List.eq_nil_iff_forall_not_mem]
    intro config member
    obtain ⟨lengthLe, gapLt, survives⟩ := mem_survivors.1 member
    exact survives (closed config lengthLe gapLt)

/-- **The finite check does not close the symmetric case by itself**: already
the strand of length three between coordinates at distance zero (both stubs at
one attachment vertex; closing lengths `3` and `6`) survives at every window
order.  The survivor lists at the manuscript's order are computed by
`#eval survivors 13 bound`; the audit records them. -/
theorem three_zero_survives : (Configuration.mk 3 0).Survives := by
  decide

/-- Conversely every strand pair whose common length is a power of two with
exponent at least two — `4, 8, 16, …` — is closed by its pair cycle, at every
gap and every order. -/
theorem survives_length_not_powerOfTwo {config : Configuration}
    (survives : config.Survives) : ¬ PowerOfTwoLength config.length :=
  fun dyadic => survives (dyadicallyClosed_of_powerOfTwo_length config dyadic)

end Hypostructure.Graph.TwoStrand
