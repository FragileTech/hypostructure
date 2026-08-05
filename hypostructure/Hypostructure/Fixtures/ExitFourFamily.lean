import Hypostructure.Graph.ExitFourFamily

/-!
# Fixture: the canonical exit-`(4)` family, its witnesses, and the peel descent

`Graph.ExitFour.Family` is the manuscript's `𝒬₄(w)`; this fixture checks the
four things a node consuming it relies on, all at an arbitrary target
predicate, an arbitrary reading, an arbitrary carrier universe and an arbitrary
generation predicate:

* a target-defective generated member whose declared support contains the
  canonical coordinate of a routed load is an exit-`(4)` witness for that load,
  and exit `(4)` occurs (`def:typeA-exit4-peeling`, `def:typeA-saturated-exits`
  exit (4));
* adjoining one witnessed unpeeled load to a peeling set is again a peeling set
  and drops `L₄(w)` by exactly one (`lem:typeA-exit4-discharge`);
* the descent that opens terminates at a peeling set -- every load of which
  carries its own witness -- leaving the receiver unsaturated, which by
  `lem:typeA-exit4-peeling-charge` is the nonnegative remaining charge node
  `[102]` returns to node `[89]`;
* clause (Q5) really is a member: a deletion at an essential carrier of the
  reading is target-defective, so a family listing that construction realizes
  exit `(4)`.

No graph family, threshold, manuscript node, or proof appears.
-/

namespace Hypostructure.Fixtures.ExitFourFamily

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.ExitFour

universe u

variable {Target : FiniteObject.{u} → Prop} {object : FiniteObject.{u}}
variable {support : Finset object.Vertex} {threshold scale : Nat}
variable {receiver : object.Vertex} {Carrier : Type u}
variable (family : Family Target support threshold receiver Carrier)

attribute [local instance] vertexDecEq

/-- **A defective member at a declared load is an exit-`(4)` witness**, and it
makes exit `(4)` occur. -/
theorem witness_of_defective
    {clause : Clause} {base identified : Finset family.entry.Coordinate}
    (defective : family.Defective clause base identified)
    {load : object.Vertex}
    (routed : load ∈ routedLoads support threshold receiver)
    (declared : family.coordinate load ∈ identified) :
    family.Witness load ∧ family.Occurs := by
  have witness : family.Witness load :=
    ⟨clause, base, identified, defective,
      family.mem_declaredLoads.mpr ⟨routed, declared⟩⟩
  exact ⟨witness, family.occurs_of_witness witness⟩

/-- **`lem:typeA-exit4-discharge`**: the enlarged peeling set is a peeling set
and the residual load drops by exactly one. -/
theorem discharge_drops_residual_by_one
    {peeled : Finset object.Vertex} (peeling : family.IsPeeling peeled)
    {load : object.Vertex} (witness : family.Witness load)
    (fresh : load ∉ peeled) :
    family.IsPeeling (insert load peeled) ∧
      residualLoad support threshold receiver (insert load peeled) + 1 =
        residualLoad support threshold receiver peeled :=
  family.isPeeling_insert peeling witness fresh

/-- **Node `[102]`'s own statement, from the exit alone.**

If, at every stage at which the peeled residual is still saturated, some
unpeeled routed load carries an exit-`(4)` witness, then the descent terminates
at a peeling set of `def:typeA-exit4-peeling` -- every listed load witnessed --
whose residual leaves the receiver unsaturated, so its remaining charge
`q(w) − ¼ − ¼·L₄(w)` is nonnegative. -/
theorem peeled_charge_of_exitFour
    (step : ∀ peeled : Finset object.Vertex, family.IsPeeling peeled →
      SaturatedAfter support threshold scale receiver peeled →
      ∃ load ∈ unpeeledLoads support threshold receiver peeled,
        family.Witness load) :
    ∃ peeled : Finset object.Vertex, family.IsPeeling peeled ∧
      1 + residualLoad support threshold receiver peeled ≤
        scale * object.missingPorts support threshold receiver := by
  obtain ⟨peeled, peeling, unsaturated⟩ :=
    family.exists_unsaturated_isPeeling (scale := scale) step
  exact ⟨peeled, peeling,
    (not_saturatedAfter_iff support threshold scale receiver peeled).mp
      unsaturated⟩

/-- **Clause (Q5) is a member of the family**: the deletion of an essential
carrier is target-defective, so a family whose generation predicate lists that
construction realizes exit `(4)`. -/
theorem occurs_of_carrierDeletion_clause [DecidableEq Carrier]
    {carrier : Carrier} (member : carrier ∈ family.entry.essentialCore)
    (generated : family.Generated Clause.carrierDeletion
      (family.entry.retained family.entry.essentialCore)
      (deletionIdentified family.entry carrier)) :
    family.Occurs :=
  occurs_of_carrierDeletion family member generated

end Hypostructure.Fixtures.ExitFourFamily
