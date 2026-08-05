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

`ℒ(w)` is the set whose cardinality `FiniteObject.routedLoad` already is; it is
named here because a peeling set is a subset of it, and `routedLoad_eq_card`
keeps the two definitions the same object.
-/

namespace Hypostructure.Graph.ExitFour

open Hypostructure

universe u

variable {object : FiniteObject.{u}} (support : Finset object.Vertex)
variable (threshold scale : Nat) (receiver : object.Vertex)

/-- Vertices of a finite object have decidable equality: the object's own vertex
schedule decides it.  Peeling sets are taken at this instance, which is the one
`FiniteObject.routedLoad` is already defined against. -/
def vertexDecEq (object : FiniteObject.{u}) : DecidableEq object.Vertex :=
  object.vertices.decEq

attribute [local instance] vertexDecEq

/-- **`ℒ(w) = {u : r(u) = w}`** of `def:typeA-exit4-peeling`: the full vertices
the canonical routing sends to this receiver. -/
noncomputable def routedLoads : Finset object.Vertex :=
  letI : DecidablePred fun source : object.Vertex =>
      object.internalDegree support source = threshold ∧
        object.traceReceiver? support threshold source = some receiver :=
    fun _ => Classical.propDecidable _
  support.filter fun source =>
    object.internalDegree support source = threshold ∧
      object.traceReceiver? support threshold source = some receiver

/-- `L(w)` is the size of `ℒ(w)`: the two readings are the same object. -/
theorem routedLoad_eq_card :
    object.routedLoad support threshold receiver =
      (routedLoads support threshold receiver).card := by
  unfold FiniteObject.routedLoad routedLoads
  congr 1
  ext source
  simp only [Finset.mem_filter]

/-- **`L₄(w) = L(w) − |P₄(w)|`**, the residual load after peeling. -/
noncomputable def residualLoad (peeled : Finset object.Vertex) : Nat :=
  ((routedLoads support threshold receiver) \ peeled).card

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
theorem mem_sdiff_iff {peeled : Finset object.Vertex}
    {load : object.Vertex} :
    load ∈ (routedLoads support threshold receiver) \ peeled ↔
      load ∈ routedLoads support threshold receiver ∧ load ∉ peeled :=
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
    (unpeeled : load ∈ (routedLoads support threshold receiver) \ peeled) :
    residualLoad support threshold receiver (insert load peeled) + 1 =
      residualLoad support threshold receiver peeled := by
  have erase :
      (routedLoads support threshold receiver) \ insert load peeled =
        ((routedLoads support threshold receiver) \ peeled).erase load := by
    ext other
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase,
      not_or]
    tauto
  rw [residualLoad, residualLoad, erase,
    Finset.card_erase_of_mem unpeeled]
  have positive :
      0 < ((routedLoads support threshold receiver) \ peeled).card :=
    Finset.card_pos.mpr ⟨load, unpeeled⟩
  omega

/-- A peeling set is a set of routed loads. -/
theorem insert_subset_routedLoads {peeled : Finset object.Vertex}
    {load : object.Vertex}
    (inside : peeled ⊆ routedLoads support threshold receiver)
    (routed : load ∈ routedLoads support threshold receiver) :
    insert load peeled ⊆ routedLoads support threshold receiver :=
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

Nothing about the witness is used beyond its load: `def:typeA-exit4-peeling`
says the witness "serves only as a routing record for its selected load". -/
theorem exists_unsaturated_peeling
    (step : ∀ peeled ⊆ routedLoads support threshold receiver,
      SaturatedAfter support threshold scale receiver peeled →
      ∃ load ∈ routedLoads support threshold receiver, load ∉ peeled) :
    ∃ peeled ⊆ routedLoads support threshold receiver,
      ¬ SaturatedAfter support threshold scale receiver peeled := by
  -- Descent on the residual load, which every peel step strictly decreases.
  suffices claim : ∀ bound : Nat,
      ∀ peeled ⊆ routedLoads support threshold receiver,
        residualLoad support threshold receiver peeled ≤ bound →
        ∃ larger ⊆ routedLoads support threshold receiver,
          ¬ SaturatedAfter support threshold scale receiver larger by
    exact claim (residualLoad support threshold receiver ∅)
      ∅ (Finset.empty_subset _) le_rfl
  intro bound
  induction bound with
  | zero =>
      intro peeled inside _small
      refine ⟨peeled, inside, ?_⟩
      intro saturated
      obtain ⟨load, routed, fresh⟩ := step peeled inside saturated
      have positive :
          0 < residualLoad support threshold receiver peeled :=
        Finset.card_pos.mpr ⟨load, Finset.mem_sdiff.mpr ⟨routed, fresh⟩⟩
      omega
  | succ bound inductionHypothesis =>
      intro peeled inside small
      by_cases saturated :
          SaturatedAfter support threshold scale receiver peeled
      · obtain ⟨load, routed, fresh⟩ := step peeled inside saturated
        have unpeeled : load ∈ (routedLoads support threshold receiver) \ peeled :=
          Finset.mem_sdiff.mpr ⟨routed, fresh⟩
        refine inductionHypothesis (insert load peeled)
          (insert_subset_routedLoads support threshold receiver inside routed) ?_
        have drop :=
          residualLoad_insert support threshold receiver unpeeled
        omega
      · exact ⟨peeled, inside, saturated⟩

end Hypostructure.Graph.ExitFour
