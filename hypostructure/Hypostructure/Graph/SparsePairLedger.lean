import Hypostructure.Graph.CanonicalFibreLedger
import Hypostructure.Graph.ExcessPortFamily

/-!
# The pair schedule of the active surplus family, and its canonical ledgers

`[130]`'s `Π(𝒜₀) = C(𝒜₀,2)` at the excess selector, and
`def:canonical-blocker-ledger` / `def:capacity-token-ledger` read on it.

Everything below is `CanonicalFibreLedger`'s single implementation, specialized
to the demands the sparse branch actually charges -- the unordered pairs of
selected ports -- so that a statement about them carries its own decidability
from the object's own vertex schedule rather than from an ambient instance.  The
label alphabet stays a parameter: it is `def:surplus-blockers`' closed clause
list at one node and `def:capacity-token-ledger`'s token universe at the next,
and the identities are the same theorem.
-/

namespace Hypostructure.Graph

universe u uLabel

namespace FiniteObject

/-- The object's own decidable equality on ordered vertex pairs.  Every
declaration below installs *this* instance, so the pair schedule, its two sides
and its fibre counts are literally the same `Finset` operations rather than
merely equal ones. -/
noncomputable def vertexPairDecidableEq (object : FiniteObject.{u}) :
    DecidableEq (object.Vertex × object.Vertex) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  infer_instance

/-- **`Π(𝒜₀)`**: the unordered pairs of selected surplus ports. -/
noncomputable def portPairSchedule (object : FiniteObject.{u})
    (threshold : Nat) : Finset (Finset (object.Vertex × object.Vertex)) := by
  letI := object.vertexPairDecidableEq
  exact Graph.CanonicalFibreLedger.pairs (object.excessPorts threshold)

/-- Every demand occurring in the canonical pair schedule is an actual member
of the selected excess-port family. -/
theorem subset_excessPorts_of_mem_portPairSchedule
    (object : FiniteObject.{u}) (threshold : Nat)
    {pair : Finset (object.Vertex × object.Vertex)}
    (member : pair ∈ object.portPairSchedule threshold) :
    pair ⊆ object.excessPorts threshold := by
  letI := object.vertexPairDecidableEq
  exact (Finset.mem_powersetCard.mp member).1

/-- **`|Π(𝒜₀)| = C(σ(G),2)`**: the pair count of the active family, at
`lem:sparse-excess-port-extraction`'s own cardinality. -/
theorem card_portPairSchedule {object : FiniteObject.{u}} {threshold : Nat}
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    (object.portPairSchedule threshold).card =
      (object.degreeSurplus threshold).choose 2 := by
  letI := object.vertexPairDecidableEq
  rw [portPairSchedule, Graph.CanonicalFibreLedger.card_pairs,
    object.card_excessPorts baseline]

/-- **`Π_blk`**: the pairs the ledger charges, each to the first declared label
that applies to it. -/
noncomputable def chargedPairs (object : FiniteObject.{u}) (threshold : Nat)
    {Label : Type uLabel} (order : List Label)
    (Applies : Label → Finset (object.Vertex × object.Vertex) → Prop)
    (decidable : ∀ label pair, Decidable (Applies label pair)) :
    Finset (Finset (object.Vertex × object.Vertex)) := by
  letI := object.vertexPairDecidableEq
  letI := decidable
  exact Graph.CanonicalFibreLedger.assigned (object.portPairSchedule threshold)
    order Applies

/-- **`Π_free`**: the complementary pairs, which no declared label applies
to. -/
noncomputable def freePairs (object : FiniteObject.{u}) (threshold : Nat)
    {Label : Type uLabel} (order : List Label)
    (Applies : Label → Finset (object.Vertex × object.Vertex) → Prop)
    (decidable : ∀ label pair, Decidable (Applies label pair)) :
    Finset (Finset (object.Vertex × object.Vertex)) := by
  letI := object.vertexPairDecidableEq
  letI := decidable
  exact Graph.CanonicalFibreLedger.unassigned
    (object.portPairSchedule threshold) order Applies

/-- **`μ(B)`, `ℓ_cap(t)`**: the fibre count of one declared label. -/
noncomputable def pairMultiplicity (object : FiniteObject.{u}) (threshold : Nat)
    {Label : Type uLabel} (labelDecidableEq : DecidableEq Label)
    (order : List Label)
    (Applies : Label → Finset (object.Vertex × object.Vertex) → Prop)
    (decidable : ∀ label pair, Decidable (Applies label pair))
    (label : Label) : Nat := by
  letI := object.vertexPairDecidableEq
  letI := labelDecidableEq
  letI := decidable
  exact Graph.CanonicalFibreLedger.multiplicity
    (object.portPairSchedule threshold) order Applies label

/-- **The split is exhaustive**: `|Π_blk| + |Π_free| = |Π(𝒜₀)|`. -/
theorem card_chargedPairs_add_card_freePairs {object : FiniteObject.{u}}
    {threshold : Nat} {Label : Type uLabel} (order : List Label)
    (Applies : Label → Finset (object.Vertex × object.Vertex) → Prop)
    (decidable : ∀ label pair, Decidable (Applies label pair)) :
    (object.chargedPairs threshold order Applies decidable).card +
        (object.freePairs threshold order Applies decidable).card =
      (object.portPairSchedule threshold).card := by
  letI := object.vertexPairDecidableEq
  letI := decidable
  exact Graph.CanonicalFibreLedger.card_assigned_add_card_unassigned _ _ _

/-- **`lem:canonical-blocker-ledger-no-overcount` and
`lem:token-ledger-no-overcount`**: `|Π_blk| = Σ_label multiplicity label`.

One theorem, read at a blocker alphabet by node `[134]` and at a token alphabet
by node `[136]`. -/
theorem card_chargedPairs_eq_sum_multiplicity {object : FiniteObject.{u}}
    {threshold : Nat} {Label : Type uLabel}
    (labelDecidableEq : DecidableEq Label) (order : List Label)
    (Applies : Label → Finset (object.Vertex × object.Vertex) → Prop)
    (decidable : ∀ label pair, Decidable (Applies label pair)) :
    (object.chargedPairs threshold order Applies decidable).card =
      (@List.toFinset _ labelDecidableEq order).sum
        (object.pairMultiplicity threshold labelDecidableEq order Applies
          decidable) := by
  letI := object.vertexPairDecidableEq
  letI := labelDecidableEq
  letI := decidable
  exact Graph.CanonicalFibreLedger.card_assigned_eq_sum_multiplicity _ _ _

/-- **A total assignment charges every pair.**

`Θ_cap` is total on the family it is defined on -- its last case is the
primitive carrier `κ(B_π)`, which is always available -- so the token ledger's
identity is read at the whole family rather than at the part some token happens
to cover. -/
theorem chargedPairs_eq_of_total {object : FiniteObject.{u}} {threshold : Nat}
    {Label : Type uLabel} (order : List Label)
    (Applies : Label → Finset (object.Vertex × object.Vertex) → Prop)
    (decidable : ∀ label pair, Decidable (Applies label pair))
    (total : ∀ pair ∈ object.portPairSchedule threshold,
      ∃ label ∈ order, Applies label pair) :
    object.chargedPairs threshold order Applies decidable =
      object.portPairSchedule threshold := by
  letI := object.vertexPairDecidableEq
  letI := decidable
  exact Graph.CanonicalFibreLedger.assigned_eq_of_total _ _ _ total

end FiniteObject

end Hypostructure.Graph
