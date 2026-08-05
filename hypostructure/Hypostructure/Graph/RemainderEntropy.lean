import Hypostructure.Graph.LabelledOn
import Hypostructure.Graph.WindowPacking
import Hypostructure.Graph.DeletionCriticality

/-!
# The per-vertex skeleton entropy of a normalized remainder

`def:remainder-entropy` fixes, for the remainder `R` a maximal packing leaves,

  `𝒢(R) = {labelled simple graphs on V(R) satisfying the remainder constraints
           already imposed on the branch}`,
  `η(R) = log₂|𝒢(R)| / |R|`.

The manuscript is explicit about two things.  First, the class is *local to the
residual*: its constraints are the ones the branch has already committed, not a
global family.  Second, it is used symbolically -- "no enumeration of labelled
graphs is prescribed, and only `|𝒢(R)|` is ever consumed".

So this module does exactly that: it names the class by the constraints, gives
it a cardinality, and provides no enumeration.  The two constraints below are
the two clauses a normalized remainder carries: no induced window of the
registered order anywhere inside it, and no subregion meeting the registered
baseline (the empty internal core of `def:internal-3-core`).  Both are stated
of the class member, at the registered order and threshold, so the class is a
function of `|R|` and of those two registered numbers alone.

`η(R) ≥ (1/d)·log₂ n` is never written with a logarithm.  Exponentiating both
sides by `d·|R|` turns it into the integer comparison

  `n ^ |R| ≤ |𝒢(R)| ^ d`,

which is what `AtLeastEntropyRate` states and what node `[50]` decides.  No
real number, division, or rounding occurs anywhere in the split.
-/

namespace Hypostructure.Graph

universe u

/-- **`𝒢(X)` of `def:remainder-entropy`.**  The labelled simple graphs on a
fixed vertex count carrying the two constraints a normalized remainder has:
window-freeness at the registered order, and no subregion at the registered
baseline.

The vertex count is the only thing the class knows about the branch's actual
remainder — `def:remainder-entropy`'s "every candidate carries the same
inherited vertex set". -/
def RemainderClass (order threshold size : Nat) : Type :=
  {member : LabelledOn size //
    (∀ support : Finset (Fin size),
      ¬ member.toFiniteObject.InducesWindow order support) ∧
    ∀ support : Finset (Fin size),
      ¬ MinimumDegreeAtLeast threshold (member.toFiniteObject.induce support)}

namespace RemainderClass

instance instFinite (order threshold size : Nat) :
    Finite (RemainderClass order threshold size) :=
  Subtype.finite

end RemainderClass

/-- **`|𝒢(X)|`.**  The only quantity `def:remainder-entropy` ever consumes. -/
noncomputable def remainderStateCount (order threshold size : Nat) : Nat :=
  Nat.card (RemainderClass order threshold size)

/-- `𝒢(X)` sits inside the ambient labelled class on the same vertex count, so
its count never exceeds `|𝒢_{|R|}|`.  This is the containment
`lem:skeleton-dominates` is stated against; nothing here needs its sharper
near-cubic form. -/
theorem remainderStateCount_le_card_labelledOn (order threshold size : Nat) :
    remainderStateCount order threshold size ≤ Nat.card (LabelledOn size) := by
  classical
  exact Nat.card_le_card_of_injective (fun member => member.val)
    Subtype.val_injective

/-- **`η(X) ≥ (1/d)·log₂ n`, exponentiated.**

Multiplying `log₂|𝒢| / |R| ≥ (log₂ n) / d` by the positive `d·|R|` and
exponentiating base two gives `n ^ |R| ≤ |𝒢| ^ d`, which is this predicate.
The manuscript's own high-entropy display is its left-hand side: the realized
remainder states number at least `2^{η(R)|R|} ≥ n^{|R|/d}`. -/
def AtLeastEntropyRate (ambientOrder denominator order threshold size : Nat) :
    Prop :=
  ambientOrder ^ size ≤ remainderStateCount order threshold size ^ denominator

/-- The low-entropy side, the exact negation. -/
def BelowEntropyRate (ambientOrder denominator order threshold size : Nat) :
    Prop :=
  remainderStateCount order threshold size ^ denominator <
    ambientOrder ^ size

theorem not_atLeastEntropyRate_iff
    (ambientOrder denominator order threshold size : Nat) :
    ¬ AtLeastEntropyRate ambientOrder denominator order threshold size ↔
      BelowEntropyRate ambientOrder denominator order threshold size :=
  Nat.not_le

end Hypostructure.Graph
