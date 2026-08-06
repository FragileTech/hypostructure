import Hypostructure.Graph.ReceiverRouting

/-!
# Exit-(4) peeling at a receiver

`def:typeA-exit4-peeling` gives a receiver `w` its routed loads
`ℒ(w) = {u : r(u) = w}`, a *peeling set* `P₄(w) ⊆ ℒ(w)` of loads that have left
the pure Type A calculation through exit `(4)`, and the residual load
`L₄(w) = L(w) − |P₄(w)|`.

Three statements are proved about that ledger, and they are the manuscript's:

* `lem:typeA-exit4-peeling-charge` -- after peeling, the remaining receiver
  charge is `q(w) − ¼ − ¼·L₄(w)`, and it is nonnegative exactly when
  `L₄(w) ≤ 4q(w) − 1`.  Cleared of the quarter, that is
  `1 + L₄(w) ≤ scale·q(w)`, which is the negation of `Saturated` read at the
  peeled residual;
* `lem:typeA-exit4-discharge` -- adjoining one unpeeled load to the peeling set
  is again a peeling set and drops `L₄(w)` by exactly one, so the remaining
  deficit falls by exactly one quarter;
* `lem:typeA-exit4-residual-routing` with the peel step -- while the peeled
  residual is still saturated, exit `(4)` supplies a fresh unpeeled load, and
  that descent terminates: some peeling set leaves the receiver unsaturated.

`ℒ(w)` of `def:typeA-exit4-peeling` is `FiniteObject.routedLoads`, which the
routing module owns: `L(w)` is its cardinality by definition, so a peeling set
is a subset of the very set the load counts.
-/

namespace Hypostructure.Graph.ExitFour

open Hypostructure

universe u

variable {object : FiniteObject.{u}} (support : Finset object.Vertex)
variable (threshold scale : Nat) (receiver : object.Vertex)

attribute [local instance] vertexDecEq

/-- **The unpeeled routed loads `ℒ(w) ∖ P₄(w)`**: the loads still charged to the
receiver after peeling. -/
noncomputable def unpeeledLoads (peeled : Finset object.Vertex) :
    Finset object.Vertex :=
  (object.routedLoads support threshold receiver) \ peeled

/-- **`L₄(w) = L(w) − |P₄(w)|`**, the residual load after peeling. -/
noncomputable def residualLoad (peeled : Finset object.Vertex) : Nat :=
  (unpeeledLoads support threshold receiver peeled).card

/-- **The receiver is still saturated at the peeled residual**: its residual load
has reached the registered multiple of its port count.  This is
`FiniteObject.Saturated` read at `L₄(w)` instead of `L(w)`. -/
def SaturatedAfter (peeled : Finset object.Vertex) : Prop :=
  scale * object.missingPorts support threshold receiver ≤
    residualLoad support threshold receiver peeled

/-- **`lem:typeA-exit4-peeling-charge`.**

*"After the loads in `P₄(w)` have left the Type A receiver calculation through
exit (4), the remaining receiver charge is `q(w) − ¼ − ¼·L₄(w)`.  In particular,
if `L₄(w) ≤ 4q(w) − 1`, then the remaining charge at `w` is nonnegative."*

Multiplied by the scale the quarter disappears and the charge is nonnegative
exactly when the peeled residual is unsaturated -- which is how the receiver is
retested at node `[89]`. -/
theorem not_saturatedAfter_iff (peeled : Finset object.Vertex) :
    ¬ SaturatedAfter support threshold scale receiver peeled ↔
      1 + residualLoad support threshold receiver peeled ≤
        scale * object.missingPorts support threshold receiver := by
  unfold SaturatedAfter
  omega

/-- An unpeeled load is a routed load that has not been peeled. -/
theorem mem_unpeeledLoads {peeled : Finset object.Vertex}
    {load : object.Vertex} :
    load ∈ unpeeledLoads support threshold receiver peeled ↔
      load ∈ object.routedLoads support threshold receiver ∧ load ∉ peeled :=
  Finset.mem_sdiff

/-- **`lem:typeA-exit4-discharge`.**

*"If exit (4) occurs through a quotient whose declared support contains the
canonical coordinate of an unpeeled routed load `u`, then `P₄(w) ∪ {u}` is a
valid peeling set and the remaining receiver deficit is reduced by exactly
`1/4`."*

Adjoining an unpeeled load preserves the no-duplicate condition of
`def:typeA-exit4-peeling` -- the load was not in the set -- and drops `L₄(w)` by
exactly one, which by `lem:typeA-exit4-peeling-charge` is exactly one quarter of
remaining deficit. -/
theorem residualLoad_insert {peeled : Finset object.Vertex}
    {load : object.Vertex}
    (unpeeled : load ∈ unpeeledLoads support threshold receiver peeled) :
    residualLoad support threshold receiver (insert load peeled) + 1 =
      residualLoad support threshold receiver peeled := by
  have erase :
      (object.routedLoads support threshold receiver) \ insert load peeled =
        ((object.routedLoads support threshold receiver) \ peeled).erase load := by
    ext other
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase,
      not_or]
    tauto
  rw [residualLoad, residualLoad, unpeeledLoads, unpeeledLoads, erase,
    Finset.card_erase_of_mem (by simpa [unpeeledLoads] using unpeeled)]
  have positive :
      0 < (unpeeledLoads support threshold receiver peeled).card :=
    Finset.card_pos.mpr ⟨load, unpeeled⟩
  rw [unpeeledLoads] at positive
  omega

/-- A peeling set is a set of routed loads. -/
theorem insert_subset_routedLoads {peeled : Finset object.Vertex}
    {load : object.Vertex}
    (inside : peeled ⊆ object.routedLoads support threshold receiver)
    (routed : load ∈ object.routedLoads support threshold receiver) :
    insert load peeled ⊆ object.routedLoads support threshold receiver :=
  Finset.insert_subset routed inside

/-- **`lem:typeA-exit4-residual-routing`, with the descent it opens.**

*"If `L₄(w) ≥ 4q(w)`, then the unpeeled routed loads at `w` realize one of exits
(1)--(8).  If the realized exit is (4), the peeling set can be enlarged by one
additional unpeeled routed load."*

`step` is that reading: while the peeled residual is still saturated, exit `(4)`
supplies a fresh unpeeled load.  Each enlargement drops `L₄(w)` by exactly one
(`residualLoad_insert`), so the descent terminates, and it terminates at a
peeling set whose residual is unsaturated -- the receiver retested at node
`[89]` with nonnegative charge.

`Retained` is whatever the peeling set is required to carry along the descent;
`def:typeA-exit4-peeling` equips each listed load with one exit-`(4)` witness,
which is `ExitFour.Family.IsPeeling`, and the descent preserves it because each
step supplies its own witness. -/
theorem exists_unsaturated_peeling
    {Retained : Finset object.Vertex → Prop} (empty : Retained ∅)
    (step : ∀ peeled ⊆ object.routedLoads support threshold receiver, Retained peeled →
      SaturatedAfter support threshold scale receiver peeled →
      ∃ load ∈ object.routedLoads support threshold receiver,
        load ∉ peeled ∧ Retained (insert load peeled)) :
    ∃ peeled ⊆ object.routedLoads support threshold receiver,
      Retained peeled ∧
        ¬ SaturatedAfter support threshold scale receiver peeled := by
  -- Descent on the residual load, which every peel step strictly decreases.
  suffices claim : ∀ bound : Nat,
      ∀ peeled ⊆ object.routedLoads support threshold receiver, Retained peeled →
        residualLoad support threshold receiver peeled ≤ bound →
        ∃ larger ⊆ object.routedLoads support threshold receiver,
          Retained larger ∧
            ¬ SaturatedAfter support threshold scale receiver larger by
    exact claim (residualLoad support threshold receiver ∅)
      ∅ (Finset.empty_subset _) empty le_rfl
  intro bound
  induction bound with
  | zero =>
      intro peeled inside retained _small
      refine ⟨peeled, inside, retained, ?_⟩
      intro saturated
      obtain ⟨load, routed, fresh, _⟩ := step peeled inside retained saturated
      have positive :
          0 < residualLoad support threshold receiver peeled :=
        Finset.card_pos.mpr ⟨load, Finset.mem_sdiff.mpr ⟨routed, fresh⟩⟩
      omega
  | succ bound inductionHypothesis =>
      intro peeled inside retained small
      by_cases saturated :
          SaturatedAfter support threshold scale receiver peeled
      · obtain ⟨load, routed, fresh, larger⟩ :=
          step peeled inside retained saturated
        have unpeeled : load ∈ unpeeledLoads support threshold receiver peeled :=
          Finset.mem_sdiff.mpr ⟨routed, fresh⟩
        refine inductionHypothesis (insert load peeled)
          (insert_subset_routedLoads support threshold receiver inside routed)
          larger ?_
        have drop :=
          residualLoad_insert support threshold receiver unpeeled
        omega
      · exact ⟨peeled, inside, retained, saturated⟩

end Hypostructure.Graph.ExitFour
