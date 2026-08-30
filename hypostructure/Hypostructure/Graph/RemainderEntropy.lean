import Hypostructure.Graph.LabelledOn
import Hypostructure.Graph.WindowPacking
import Hypostructure.Graph.DeletionCriticality
import Hypostructure.Graph.WedgeLowerBound

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
it a cardinality, and provides no enumeration.  A candidate has no induced
window of the registered order, no subregion meeting the registered baseline,
and no more positive deficiency than the literal incoming remainder.  A
maximum-degree bound is not among the incoming facts and is therefore not part
of the class.  The last
parameter is essential: without it `𝒢(R)` silently forgets a branch-local
ledger constraint and is not the class used by `def:remainder-entropy`.

`η(R) ≥ (1/d)·log₂ n` is never written with a logarithm.  Exponentiating both
sides by `d·|R|` turns it into the integer comparison

  `n ^ |R| ≤ |𝒢(R)| ^ d`,

which is what `AtLeastEntropyRate` states and what node `[50]` decides.  No
real number, division, or rounding occurs anywhere in the split.
-/

namespace Hypostructure.Graph

universe u

/-- **`𝒢(X)` of `def:remainder-entropy`.**  The labelled simple graphs on the
inherited vertex set carrying "the remainder constraints already imposed on the
branch": window-freeness at the registered order (componentwise
`P₁₃`-freeness), no subregion at the registered baseline (no internal `3`-core),
positive deficiency at most the inherited cap, and — "every candidate carries
the same inherited vertex set, so the density comparison is equivalently the
comparison of its net-deficiency numerator with the inherited one" — the
inherited edge count.  The last constraint is the branch's *glue*: a candidate
with the inherited edge count replaces the object's own remainder inside the
object without changing the vertex or edge count, which is what makes `𝒢(X)`
a subclass of the labelled skeleton class `𝒢_{n,m}` (`RemainderGlue`).  There
is deliberately no maximum-degree conjunct: the incoming normalized-remainder
fact excludes an internal baseline core, which does not imply a maximum-degree
bound (a star is the elementary counterexample). -/
def RemainderClass (order threshold deficiencyCap edgeCount size : Nat) : Type :=
  {member : LabelledOn size //
    (∀ support : Finset (Fin size),
      ¬ member.toFiniteObject.InducesWindow order support) ∧
    (∀ support : Finset (Fin size),
      ¬ MinimumDegreeAtLeast threshold (member.toFiniteObject.induce support)) ∧
    member.toFiniteObject.positiveDeficiency
      (Finset.univ : Finset (Fin size)) threshold ≤ deficiencyCap ∧
    Nat.card member.graph.edgeSet = edgeCount}

namespace RemainderClass

instance instFinite (order threshold deficiencyCap edgeCount size : Nat) :
    Finite (RemainderClass order threshold deficiencyCap edgeCount size) :=
  Subtype.finite

end RemainderClass

/-- **`|𝒢(X)|`.**  The only quantity `def:remainder-entropy` ever consumes. -/
noncomputable def remainderStateCount
    (order threshold deficiencyCap edgeCount size : Nat) : Nat :=
  Nat.card (RemainderClass order threshold deficiencyCap edgeCount size)

/-- `𝒢(X)` sits inside the ambient labelled class on the same vertex count, so
its count never exceeds `|𝒢_{|R|}|`.  This is the containment
`lem:skeleton-dominates` is stated against; nothing here needs its sharper
near-cubic form. -/
theorem remainderStateCount_le_card_labelledOn
    (order threshold deficiencyCap edgeCount size : Nat) :
    remainderStateCount order threshold deficiencyCap edgeCount size ≤
      Nat.card (LabelledOn size) := by
  classical
  exact Nat.card_le_card_of_injective (fun member => member.val)
    Subtype.val_injective

/-- **`η(X) ≥ (1/d)·log₂ n`, exponentiated.**

Multiplying `log₂|𝒢| / |R| ≥ (log₂ n) / d` by the positive `d·|R|` and
exponentiating base two gives `n ^ |R| ≤ |𝒢| ^ d`, which is this predicate.
The manuscript's own high-entropy display is its left-hand side: the realized
remainder states number at least `2^{η(R)|R|} ≥ n^{|R|/d}`. -/
def AtLeastEntropyRate
    (ambientOrder denominator order threshold deficiencyCap edgeCount size : Nat) :
    Prop :=
  ambientOrder ^ size ≤
    remainderStateCount order threshold deficiencyCap edgeCount size ^ denominator

/-- The low-entropy side, the exact negation. -/
def BelowEntropyRate
    (ambientOrder denominator order threshold deficiencyCap edgeCount size : Nat) :
    Prop :=
  remainderStateCount order threshold deficiencyCap edgeCount size ^ denominator <
    ambientOrder ^ size

theorem not_atLeastEntropyRate_iff
    (ambientOrder denominator order threshold deficiencyCap edgeCount size : Nat) :
    ¬ AtLeastEntropyRate ambientOrder denominator order threshold deficiencyCap
        edgeCount size ↔
      BelowEntropyRate ambientOrder denominator order threshold deficiencyCap
        edgeCount size :=
  Nat.not_le

end Hypostructure.Graph
