import Hypostructure.Graph.ReceiverLoad
import Hypostructure.Graph.ReceiverExhaustion
import Hypostructure.Graph.TypeABCertificate

/-!
# Type A receiver discharge

`lem:typeA-unsaturated-discharge` and its charge algebra, manuscript nodes
`[90]`--`[92]` of Figure 8.

The receiver ledger of `Hypostructure.Graph.ReceiverLoad` already carries every
carrier this argument needs: the internal support degree, the receiver classes,
the missing-port count `q(w)`, the canonical routed load `L(w)`, and the
saturation predicates.  It also already proves the two combinatorial facts the
discharge rests on -- `RoutedLoad.total_load_eq_full_card`, that every full-load
vertex is routed to exactly one receiver, and
`RoutedLoad.unsaturated_capacity_bound`, that the unsaturated hypothesis caps the
full-load count by the receivers' capacity.

What is added here is the charge algebra that turns that capacity bound into the
manuscript's deficiency statement

  `def⁺(X) ≥ α · |V(X)|`,   `α = 1 / loadMultiplier`,

equivalently `|V(X)| ≤ loadMultiplier · def⁺(X)`.  No numeral is written: the
manuscript's `3/7/11` coefficients are `loadMultiplier * q(w) - 1` evaluated at
the three receiver classes `q(w) ∈ {1, 2, 3}`, and the manuscript's `α = 1/4` is
the registered `LoadCapacityProfile.dischargeRate`.
-/

namespace Hypostructure.Graph.TypeAReceiverClosure

universe u

open Hypostructure
open Hypostructure.Graph.ReceiverLoad

/-! ## The registered profile discharges by a whole port

`lem:typeA-unsaturated-discharge` needs the capacity `loadMultiplier * q(w)` of a
receiver to be at least one, so that the unsaturated bound `L(w) ≤ 4q(w) - 1`
loses exactly one unit rather than saturating Nat subtraction.  Both halves come
from data the profile already carries. -/

/-- The registered discharge window forces a positive overload factor.  At
`loadMultiplier = 0` the rate `1 / 0` is `0` in `ℚ`, so `dischargeRate_gt`'s
`1 < 5 / loadMultiplier` fails outright: a profile that discharges nothing is
not a profile. -/
theorem loadMultiplier_pos (profile : LoadCapacityProfile) :
    0 < profile.loadMultiplier := by
  rcases Nat.eq_zero_or_pos profile.loadMultiplier with zero | pos
  · exfalso
    have constraint := profile.dischargeRate_gt
    rw [zero] at constraint
    norm_num at constraint
  · exact pos

variable {object : FiniteObject.{u}}

/-- Decidable equality on the full-load class, inherited from the object's own
vertex decision procedure.  Stating the exit-(4) peel needs `Finset` difference
on this class, so the instance has to be available in statements and not only
inside proofs. -/
instance instDecidableEqFullVertex {support : Support object}
    {profile : LoadCapacityProfile} :
    DecidableEq (support.FullVertex profile) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  infer_instance

/-- A receiver is missing at least one port.  This is the defining property of
`ReceiverVertex` read through `missingPorts`. -/
theorem missingPorts_pos {support : Support object} {profile : LoadCapacityProfile}
    (receiver : support.ReceiverVertex profile) :
    0 < support.missingPorts profile receiver := by
  have deficient : support.internalDegree receiver.1 < profile.baselineDegree :=
    receiver.2.2
  unfold Support.missingPorts
  omega

/-- The receiver's capacity is at least one whole routed load. -/
theorem one_le_capacity {support : Support object} {profile : LoadCapacityProfile}
    (receiver : support.ReceiverVertex profile) :
    1 ≤ profile.loadMultiplier * support.missingPorts profile receiver :=
  Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero
      (Nat.pos_iff_ne_zero.mp (loadMultiplier_pos profile))
      (Nat.pos_iff_ne_zero.mp (missingPorts_pos receiver)))

/-! ## `lem:typeA-threshold-algebra`, manuscript node `[88]`

The manuscript's raw threshold at a receiver of class `R_j(X)` -- where
`d_X(w) = 2 - j` and so `q(w) = j + 1` -- is

  `H_j = 4 q(w) = 4(j + 1)`,

"the first routed load value at which `w` leaves the unsaturated Type A
discharging branch", giving `H_0 ≤ 4`, `H_1 ≤ 8`, `H_2 ≤ 12`.

In the ledger that value is not a new quantity: it is the saturation threshold
already carried by `RoutedLoad.saturated`.  The three statements below say
exactly that, so node `[88]` records an observable rather than introducing a
constant. -/

/-- The manuscript's raw threshold `H_j = loadMultiplier · q(w)`. -/
noncomputable def threshold {support : Support object}
    (profile : LoadCapacityProfile)
    (receiver : support.ReceiverVertex profile) : Nat :=
  profile.loadMultiplier * support.missingPorts profile receiver

/-- `H_j` is the value at which the receiver becomes saturated. -/
theorem saturated_iff_threshold_le {support : Support object}
    {profile : LoadCapacityProfile}
    (routing : RoutedLoad (object := object) profile support)
    (receiver : support.ReceiverVertex profile) :
    routing.saturated receiver ↔
      threshold profile receiver ≤ routing.load receiver := Iff.rfl

/-- `L(w) ≤ H_j - 1` is the unsaturated branch, verbatim. -/
theorem unsaturated_iff_le_threshold_pred {support : Support object}
    {profile : LoadCapacityProfile}
    (routing : RoutedLoad (object := object) profile support)
    (receiver : support.ReceiverVertex profile) :
    routing.unsaturated receiver ↔
      routing.load receiver ≤ threshold profile receiver - 1 := Iff.rfl

/-- **`lem:typeA-threshold-algebra`'s bound.**  A receiver misses at most
`baselineDegree` ports, so its raw threshold is at most
`loadMultiplier · baselineDegree`.  At the registered profile that is
`H_j ≤ 12`, with `H_0 = 4`, `H_1 = 8`, `H_2 = 12` obtained by evaluating
`q(w) = j + 1`.  No numeral is written here. -/
theorem threshold_le {support : Support object}
    {profile : LoadCapacityProfile}
    (receiver : support.ReceiverVertex profile) :
    threshold profile receiver ≤
      profile.loadMultiplier * profile.baselineDegree := by
  unfold threshold Support.missingPorts
  exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

/-! ## The deficiency of a support

`def:admissible`'s `def⁺(X)` in receiver coordinates: the total number of ports
the support's receivers are missing.  Full-load vertices contribute nothing, so
summing over the receiver class is the whole sum. -/

/-- `def⁺(X) = Σ_{w receiver} q(w)`. -/
noncomputable def deficiency (support : Support object)
    (profile : LoadCapacityProfile) : Nat :=
  ∑ receiver ∈ support.receiverVertices profile,
    support.missingPorts profile receiver

/-! ## The two support carriers agree

`Graph.Strategy.NormalizationRank.supportIncidence` counts a vertex's neighbours
inside a declared support; `ReceiverLoad.Support.internalDegree` counts the same
set from the other side.  They are equal, so the receiver ledger and the CT14
local-supply ledger measure one quantity and `TypeAB.AdmissibleNegativeSupport`'s
own `requiredMass_eq` transports between them without anything being restated. -/

theorem supportIncidence_eq_internalDegree (support : Support object)
    (vertex : object.Vertex) :
    Graph.Strategy.NormalizationRank.supportIncidence object support.core
        vertex =
      support.internalDegree vertex := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  unfold Graph.Strategy.NormalizationRank.supportIncidence Support.internalDegree
  rw [List.countP_eq_length_filter]
  rw [← List.toFinset_card_of_nodup
    ((object.orderedNeighbors_nodup vertex).filter _)]
  congr 1
  ext candidate
  simp [List.mem_toFinset, object.mem_orderedNeighbors_iff, Finset.mem_filter]
  tauto

/-- Internal degree never exceeds ambient degree: the support neighbours are a
sublist of all neighbours. -/
theorem internalDegree_le_degree (support : Support object)
    (vertex : object.Vertex) :
    support.internalDegree vertex ≤ object.degree vertex := by
  rw [← supportIncidence_eq_internalDegree,
    ← object.orderedNeighbors_length vertex]
  unfold Graph.Strategy.NormalizationRank.supportIncidence
  exact List.countP_le_length

/-- **`def:typeA-support`'s subcubicity.**  On a Type A support `σ(X) = 0` forces
every member's ambient degree to the baseline, so its internal degree is at most
the baseline -- the hypothesis `unsaturated_discharge_core` needs, read off the
certificate's own `ambientCubic` field rather than assumed. -/
theorem internalDegree_le_baseline_of_ambientCubic (support : Support object)
    (profile : LoadCapacityProfile)
    (ambientCubic : ∀ vertex ∈ support.core,
      object.degree vertex = profile.baselineDegree) :
    ∀ vertex ∈ support.core,
      support.internalDegree vertex ≤ profile.baselineDegree := by
  intro vertex member
  rw [← ambientCubic vertex member]
  exact internalDegree_le_degree support vertex

/-- The receiver-class sum written over the support's own filter, so it can be
compared with `TypeAB.positiveDeficiency` without leaving `Finset`. -/
theorem deficiency_eq_filterSum (support : Support object)
    (profile : LoadCapacityProfile) :
    deficiency support profile =
      ∑ vertex ∈ support.core.filter
          (fun v => support.internalDegree v < profile.baselineDegree),
        (profile.baselineDegree - support.internalDegree vertex) := by
  classical
  unfold deficiency Support.missingPorts Support.receiverVertices
  rw [Finset.sum_subtype (p := fun v =>
      v ∈ support.core ∧ support.internalDegree v < profile.baselineDegree)]
  intro vertex
  simp

/-- The receiver-class sum is the framework's own `def⁺(X)`.

`TypeAB.positiveDeficiency` is the registered CT14 required-mass observation
aggregated over the support; the receiver ledger sums the same per-vertex
quantity over the receiver class, and full-load members contribute nothing.  So
the two agree, and `AdmissibleNegativeSupport.requiredMass_eq` -- the framework's
own bridge to `summary.requiredMass` -- is the only transport needed.  Nothing
here re-routes: `supportIncidence_eq_internalDegree` identifies the two incidence
counts and the split is `Finset.sum_filter_add_sum_filter_not`. -/
theorem receiverSum_eq_positiveDeficiency
    {presentation : TypeAB.Presentation.{u}}
    (support : Support object) (profile : LoadCapacityProfile)
    (baseline : presentation.baselineDegree = profile.baselineDegree) :
    ∑ vertex ∈ support.core.filter
        (fun v => support.internalDegree v < profile.baselineDegree),
      (profile.baselineDegree - support.internalDegree vertex) =
      TypeAB.positiveDeficiency presentation object support.core := by
  classical
  unfold TypeAB.positiveDeficiency
  rw [← Finset.sum_filter_add_sum_filter_not support.core
    (fun v => support.internalDegree v < profile.baselineDegree)]
  have vanishes : ∀ vertex ∈ support.core.filter
      (fun v => ¬ support.internalDegree v < profile.baselineDegree),
      presentation.baselineDegree -
        Graph.Strategy.NormalizationRank.supportIncidence object support.core
          vertex = 0 := by
    intro vertex member
    have notLess := (Finset.mem_filter.mp member).2
    rw [supportIncidence_eq_internalDegree, baseline]
    omega
  rw [Finset.sum_congr rfl vanishes, Finset.sum_const_zero, Nat.add_zero]
  refine Finset.sum_congr rfl ?_
  intro vertex _member
  rw [supportIncidence_eq_internalDegree, baseline]

/-! ## `lem:typeA-unsaturated-discharge` -/

/-- **`lem:typeA-unsaturated-discharge`, manuscript nodes `[90]`--`[91]`.**

If every receiver of the support is unsaturated, then the support's vertex count
is at most `loadMultiplier` times its deficiency:

  `|V(X)| ≤ loadMultiplier · def⁺(X)`,

which is the manuscript's `def⁺(X) ≥ α|V(X)|` with `α = 1 / loadMultiplier`
cleared of its denominator.

The proof is the manuscript's discharging rule, carried out on the ledger rather
than beside it.  `RoutedLoad.unsaturated_capacity_bound` gives
`n₃ ≤ Σ_w (m·q(w) − 1)`; adding back the one unit each receiver withheld turns
the right-hand side into `Σ_w m·q(w)`, and the left-hand side into the full
vertex count `n₃ + |receivers|`.  The subtraction is exact because
`one_le_capacity` says every receiver's capacity is at least the unit being
withheld.

At the registered profile (`baselineDegree = 3`, `loadMultiplier = 4`) the
receiver classes are `q(w) ∈ {1, 2, 3}` for `d_X(w) ∈ {2, 1, 0}`, so
`m·q(w) − 1` is `3`, `7`, `11` respectively and this statement is literally the
manuscript's `n₃ ≤ 3n₂ + 7n₁ + 11n₀`.  Those coefficients are computed here, not
written. -/
theorem unsaturated_discharge {support : Support object}
    {profile : LoadCapacityProfile}
    (routing : RoutedLoad (object := object) profile support)
    (unsaturated : ∀ receiver : support.ReceiverVertex profile,
      routing.unsaturated receiver) :
    (support.fullVertices profile).card +
        (support.receiverVertices profile).card ≤
      profile.loadMultiplier * deficiency support profile := by
  classical
  have capacity := routing.unsaturated_capacity_bound unsaturated
  have restore : ∀ receiver ∈ support.receiverVertices profile,
      profile.loadMultiplier * support.missingPorts profile receiver - 1 + 1 =
        profile.loadMultiplier * support.missingPorts profile receiver := by
    intro receiver _member
    have unit := one_le_capacity (support := support) (profile := profile) receiver
    omega
  calc
    (support.fullVertices profile).card +
          (support.receiverVertices profile).card
        ≤ (∑ receiver ∈ support.receiverVertices profile,
              (profile.loadMultiplier *
                support.missingPorts profile receiver - 1)) +
            (support.receiverVertices profile).card := by
          exact Nat.add_le_add_right capacity _
    _ = ∑ receiver ∈ support.receiverVertices profile,
          (profile.loadMultiplier *
            support.missingPorts profile receiver - 1 + 1) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    _ = ∑ receiver ∈ support.receiverVertices profile,
          (profile.loadMultiplier *
            support.missingPorts profile receiver) :=
          Finset.sum_congr rfl restore
    _ = profile.loadMultiplier * deficiency support profile := by
          rw [deficiency, Finset.mul_sum]

/-! ## `lem:typeA-saturated-handoff`, manuscript nodes `[89]`--`[102]`

Figure 8's only cycle is the exit-(4) back-edge `[102] → [89]`, labelled
"recompute `L₄`".  The manuscript discharges it by a descent, and that descent is
what this section proves, so the loop never has to appear in the DAG.

The manuscript's proof is: start with the peeling set `P₄(w) = ∅`; if the
residual load `L₄(w) = L(w) - |P₄(w)|` is already below `4q(w)` stop; otherwise
route, and exit (4) adds one load to `P₄(w)`, strictly decreasing `L₄(w)`; since
`L(w)` is finite the process terminates.

`peelDescent` below is exactly that induction, stated over the routed fibre of a
receiver.  `Outcome` stands for "the routing left the pure Type A discharging
branch" -- a closed exit among (1)--(3), (5), (6), the Type B handoff (7), or the
route-8 residual (8) -- and `Witness` is the exit-(4) witness each peeled load
carries (`def:typeA-exit4-peeling`).  Neither is interpreted here: the
alternatives are the caller's, exactly as `def:typeA-saturated-exits` enumerates
them. -/

section Descent

variable {α : Type u}

/-- The manuscript's exit-(4) descent, as a finite induction on the residual
load.  Either the routing leaves the discharging branch, or peeling reaches a
witnessed set after which the residual load is strictly below the threshold. -/
private theorem peelDescent [DecidableEq α]
    (fibre : Finset α) (threshold : Nat) (Outcome : Prop) (Witness : α → Prop)
    (step : ∀ peeled : Finset α, peeled ⊆ fibre →
      threshold ≤ (fibre \ peeled).card →
        Outcome ∨ ∃ element ∈ fibre \ peeled, Witness element) :
    ∀ fuel : Nat, ∀ peeled : Finset α, peeled ⊆ fibre →
      (∀ element ∈ peeled, Witness element) →
      (fibre \ peeled).card ≤ fuel →
      Outcome ∨ ∃ final : Finset α, final ⊆ fibre ∧
        (∀ element ∈ final, Witness element) ∧
        (fibre \ final).card < threshold := by
  intro fuel
  induction fuel with
  | zero =>
    intro peeled subset witnessed bound
    by_cases below : (fibre \ peeled).card < threshold
    · exact Or.inr ⟨peeled, subset, witnessed, below⟩
    · replace below := Nat.not_lt.mp below
      rcases step peeled subset below with outcome | ⟨element, member, _⟩
      · exact Or.inl outcome
      · exact absurd (Finset.card_pos.mpr ⟨element, member⟩) (by omega)
  | succ fuel ih =>
    intro peeled subset witnessed bound
    by_cases below : (fibre \ peeled).card < threshold
    · exact Or.inr ⟨peeled, subset, witnessed, below⟩
    · replace below := Nat.not_lt.mp below
      rcases step peeled subset below with outcome | ⟨element, member, witness⟩
      · exact Or.inl outcome
      · refine ih (insert element peeled) ?_ ?_ ?_
        · intro x member'
          rcases Finset.mem_insert.mp member' with rfl | member'
          · exact (Finset.mem_sdiff.mp member).1
          · exact subset member'
        · intro x member'
          rcases Finset.mem_insert.mp member' with rfl | member'
          · exact witness
          · exact witnessed x member'
        · have shrink :
              (fibre \ insert element peeled).card < (fibre \ peeled).card := by
            rw [Finset.sdiff_insert]
            exact Finset.card_erase_lt_of_mem member
          omega

end Descent

/-- The routed fibre of a receiver: the full-load members whose canonical trace
ends at it.  `RoutedLoad.load` is its cardinality by definition. -/
noncomputable def routedFibre {support : Support object}
    {profile : LoadCapacityProfile}
    (routing : RoutedLoad (object := object) profile support)
    (receiver : support.ReceiverVertex profile) :
    Finset (support.FullVertex profile) := by
  classical
  exact (support.fullVertices profile).filter
    fun full => routing.route full = receiver

theorem card_routedFibre {support : Support object}
    {profile : LoadCapacityProfile}
    (routing : RoutedLoad (object := object) profile support)
    (receiver : support.ReceiverVertex profile) :
    (routedFibre routing receiver).card = routing.load receiver := rfl

/-- **`lem:typeA-saturated-handoff`, manuscript nodes `[89]`--`[102]`.**

At a saturated receiver, repeated application of the saturated receiver routing
has one of two outcomes: the routing leaves the pure Type A discharging branch
(a closed exit among (1)--(3), (5), (6), the Type B handoff (7), or the route-8
residual (8)), or exit (4) peels finitely many routed loads and the remaining
receiver load becomes unsaturated.

This is the manuscript's "Consequently every receiver that remains in the pure
Type A discharging branch after the closed exits, exit-(4) peeling, route 8, and
the Type B handoff have been removed satisfies `L(w) ≤ 4q(w) - 1`."

The conclusion is stated at the manuscript's own inequality
`L₄(w) ≤ loadMultiplier · q(w) - 1`, which is `RoutedLoad.unsaturated` read on
the peeled fibre.  The threshold is positive by `one_le_capacity`, so the strict
and the predecessor forms agree. -/
theorem saturated_handoff {support : Support object}
    {profile : LoadCapacityProfile}
    (routing : RoutedLoad (object := object) profile support)
    (receiver : support.ReceiverVertex profile)
    (Outcome : Prop) (Witness : support.FullVertex profile → Prop)
    (step : ∀ peeled : Finset (support.FullVertex profile),
      peeled ⊆ routedFibre routing receiver →
      profile.loadMultiplier * support.missingPorts profile receiver ≤
          (routedFibre routing receiver \ peeled).card →
        Outcome ∨ ∃ element ∈ routedFibre routing receiver \ peeled,
          Witness element) :
    Outcome ∨ ∃ peeled : Finset (support.FullVertex profile),
      peeled ⊆ routedFibre routing receiver ∧
        (∀ element ∈ peeled, Witness element) ∧
        (routedFibre routing receiver \ peeled).card ≤
          profile.loadMultiplier * support.missingPorts profile receiver - 1 := by
  classical
  rcases peelDescent (routedFibre routing receiver)
      (profile.loadMultiplier * support.missingPorts profile receiver)
      Outcome Witness step (routedFibre routing receiver).card ∅
      (Finset.empty_subset _) (by simp) (by simp) with outcome | ⟨final, rest⟩
  · exact Or.inl outcome
  · exact Or.inr ⟨final, rest.1, rest.2.1, by omega⟩

/-! ## The support's own vertex count

`lem:typeA-unsaturated-discharge` is stated about `|V(X)|`, so the two receiver
classes have to exhaust the support.  They do exactly when no member has internal
degree above the baseline, which on a Type A support is automatic: `σ(X) = 0`
gives `d_G(v) = baselineDegree` for every member (`def:typeA-support`), and the
internal degree never exceeds the ambient one. -/

/-- The full-load class counts the members at exactly the baseline. -/
theorem card_fullVertices (support : Support object)
    (profile : LoadCapacityProfile) :
    (support.fullVertices profile).card =
      (support.core.filter fun vertex =>
        support.internalDegree vertex = profile.baselineDegree).card := by
  classical
  simp [Support.fullVertices, Fintype.subtype_card]

/-- The receiver class counts the members strictly below the baseline. -/
theorem card_receiverVertices (support : Support object)
    (profile : LoadCapacityProfile) :
    (support.receiverVertices profile).card =
      (support.core.filter fun vertex =>
        support.internalDegree vertex < profile.baselineDegree).card := by
  classical
  simp [Support.receiverVertices, Fintype.subtype_card]

/-- **The two receiver classes partition a subcubic support.**  `|V(X)| = n₃ +
(n₂ + n₁ + n₀)` in the manuscript's notation. -/
theorem card_core_eq (support : Support object) (profile : LoadCapacityProfile)
    (subcubic : ∀ vertex ∈ support.core,
      support.internalDegree vertex ≤ profile.baselineDegree) :
    support.core.card =
      (support.fullVertices profile).card +
        (support.receiverVertices profile).card := by
  classical
  rw [card_fullVertices, card_receiverVertices]
  have filterEq :
      support.core.filter (fun vertex =>
          ¬ support.internalDegree vertex = profile.baselineDegree) =
        support.core.filter (fun vertex =>
          support.internalDegree vertex < profile.baselineDegree) := by
    apply Finset.filter_congr
    intro vertex member
    have bound := subcubic vertex member
    omega
  rw [← filterEq, Finset.card_filter_add_card_filter_not]

/-- **`lem:typeA-unsaturated-discharge` at the manuscript's own statement.**

`|V(X)| ≤ loadMultiplier · def⁺(X)`, i.e. `def⁺(X) ≥ α|V(X)|`, for a subcubic
support all of whose receivers are unsaturated.  This is `unsaturated_discharge`
with the two receiver classes recognised as the whole support. -/
theorem unsaturated_discharge_core {support : Support object}
    {profile : LoadCapacityProfile}
    (routing : RoutedLoad (object := object) profile support)
    (unsaturated : ∀ receiver : support.ReceiverVertex profile,
      routing.unsaturated receiver)
    (subcubic : ∀ vertex ∈ support.core,
      support.internalDegree vertex ≤ profile.baselineDegree) :
    support.core.card ≤ profile.loadMultiplier * deficiency support profile := by
  rw [card_core_eq support profile subcubic]
  exact unsaturated_discharge routing unsaturated

/-- **`lem:typeA-unsaturated-discharge` on the framework's own deficiency
carrier.**

`|V(X)| ≤ loadMultiplier · def⁺(X)`, with `def⁺(X)` the registered
`TypeAB.positiveDeficiency` rather than any receiver-side restatement.  This is
the form `TypeAB.AdmissibleNegativeSupport.requiredMass_eq` transports to
`summary.requiredMass`, so the ledger reading needs no bridge of ours: the
certificate already carries the equation. -/
theorem unsaturated_discharge_positiveDeficiency
    {presentation : TypeAB.Presentation.{u}} {support : Support object}
    {profile : LoadCapacityProfile}
    (routing : RoutedLoad (object := object) profile support)
    (unsaturated : ∀ receiver : support.ReceiverVertex profile,
      routing.unsaturated receiver)
    (subcubic : ∀ vertex ∈ support.core,
      support.internalDegree vertex ≤ profile.baselineDegree)
    (baseline : presentation.baselineDegree = profile.baselineDegree) :
    support.core.card ≤
      profile.loadMultiplier *
        TypeAB.positiveDeficiency presentation object support.core := by
  have discharge := unsaturated_discharge_core routing unsaturated subcubic
  rwa [deficiency_eq_filterSum support profile,
    receiverSum_eq_positiveDeficiency (presentation := presentation) support
      profile baseline] at discharge

/-! ## The discharge in ledger coordinates

`unsaturated_discharge_core` above is the receiver-side statement.  Its ledger
reading is **not** written here.

An earlier version of this file carried a `remainder_le_multiplier_mul_requiredMass`
that took the two identifications `remainder = |V(X)|` and `requiredMass = def⁺(X)`
as hypotheses.  Those are facts about the registration's *own* member schedule,
not presentation data, so handing them in was carrying data by hand.  Once
`Graph.Strategy.TypeAReceiverExhaustion.receiverLoadLedger` is registered, Core
aggregates the same observations itself and publishes exactly
`remainder ≤ loadMultiplier · requiredMass` on the local-supply `Summary`; that
published entry is `TypeAReceiverStages.Discharge91`, and it is read off the
node-`[89]` decision rather than reconstructed.

Manuscript node `[92]`'s contradiction likewise lives beside the ledger entry it
consumes, as `Core.Strategy.LocalSupplyLowerBound.Summary.unsaturatedChargeContradiction`,
and is retrieved by `TypeAReceiverStages.contradiction92`. -/

/-! ## Manuscript node `[92]`: the unsaturated Type A charge closes

Every fact is read off `TypeAB.TypeACertificate`, the framework's own Type A
carrier.  It bundles `def:typeA-support`'s `σ(X) = 0` and ambient cubicity, the
node-`[61]` negative charge, and -- as `remainder_eq` and `requiredMass_eq` --
the two identifications between the support and the local-supply ledger entry
published for it.  So no bridge is built here and nothing is assumed: the
certificate carries the equations, `strictQuarter` turns the negative charge into
`dischargeScale · def⁺(X) < |V(X)|`, and
`unsaturated_discharge_positiveDeficiency` gives the opposite inequality. -/

/-- **Manuscript node `[92]`.**  A Type A certificate whose receivers are all
unsaturated is impossible. -/
theorem certificate_unsaturated_impossible
    {presentation : TypeAB.Presentation.{u}} {object : FiniteObject.{u}}
    {profile : LoadCapacityProfile}
    (certificate : TypeAB.TypeACertificate presentation object)
    (routing : RoutedLoad (object := object) profile
      ⟨certificate.common.support⟩)
    (unsaturated : ∀ receiver :
        (⟨certificate.common.support⟩ : Support object).ReceiverVertex profile,
      routing.unsaturated receiver)
    (baseline : presentation.baselineDegree = profile.baselineDegree)
    (scale : presentation.dischargeScale = profile.loadMultiplier) :
    False := by
  have ambientCubic : ∀ vertex ∈ certificate.common.support,
      object.degree vertex = profile.baselineDegree := by
    intro vertex member
    rw [← baseline]
    exact certificate.ambientCubic vertex member
  have subcubic := internalDegree_le_baseline_of_ambientCubic
    (⟨certificate.common.support⟩ : Support object) profile ambientCubic
  have discharge :=
    unsaturated_discharge_positiveDeficiency (presentation := presentation)
      routing unsaturated subcubic baseline
  have strict := certificate.strictQuarter
  rw [certificate.common.requiredMass_eq, certificate.common.remainder_eq,
    scale] at strict
  have coreEq : (⟨certificate.common.support⟩ : Support object).core =
      certificate.common.support := rfl
  rw [coreEq] at discharge
  omega

/-! ## Manuscript node `[106]`: the delocalization branch closes

`lem:typeA-exits-discharged` excludes exit (6) by `lem:proper-smearing` in the
proper-support case and by `lem:no-silent-global-smearing` in the whole-graph
case.  Both are the refutation of a proper baseline-preserving sub-support, and
the Type A certificate already carries that refutation as
`AdmissibleNegativeSupport.uncompressible` -- `cor:uncompressible`, which says
every such sub-support *already realizes the registered target*.

So the delocalization arm does not merely contradict something: it hands over a
target, and `CycleCertificate.mapHom` along `FiniteObject.induceEmbedding`
transports it from the sub-support to the ambient object.  Nothing is assumed
and no certificate is rebuilt. -/

/-- **Manuscript node `[106]`.**  A proper baseline-preserving sub-support of a
Type A certificate's support realizes the registered cycle target on the whole
object. -/
theorem hasCycleWithLength_of_properBaselineSubsupport
    {presentation : TypeAB.Presentation.{u}} {object : FiniteObject.{u}}
    {LengthOK : Nat → Prop}
    (certificate : TypeAB.TypeACertificate presentation object)
    (targetIsCycle : ∀ candidate : FiniteObject.{u},
      presentation.Target candidate ↔ HasCycleWithLength LengthOK candidate)
    {smaller : Finset object.Vertex}
    (nonempty : smaller.Nonempty)
    (proper : smaller ⊂ certificate.common.support)
    (baseline : TypeAB.Baseline presentation (object.induce smaller)) :
    HasCycleWithLength LengthOK object := by
  have realized : presentation.Target (object.induce smaller) :=
    certificate.common.uncompressible smaller nonempty proper baseline
  obtain ⟨cycle⟩ := (targetIsCycle (object.induce smaller)).mp realized
  exact ⟨cycle.mapHom (object.induceEmbedding smaller).toHom
    (object.induceEmbedding smaller).injective⟩

/-! ## Manuscript node `[104]`: the uncompressibility contradiction

`lem:typeA-exits-discharged` on exit (5): *"Exit (5) is a nontrivial
target-complete response compression.  If the compression is realized by a
smaller proper atom, it contradicts hereditary target-uncompressibility
(`cor:uncompressible`)."*

Node `[104]` is the terminal for that first case, and it consumes the same
certificate field as node `[106]` -- `AdmissibleNegativeSupport.uncompressible`
-- but through the exit's own extra clause rather than through a cycle
embedding.  *Target-complete* is exactly the statement that the compression
preserves the target response, so the target `cor:uncompressible` hands back at
the smaller proper atom is already a target of the ambient object: the
completeness clause is the transport, and no embedding is needed.

This is what separates `[104]` from `[106]`.  Exit (6) has no response equality
to ride on and must move a cycle along `induceEmbedding`; exit (5) carries the
equality in its own hypothesis. -/

/-- **Manuscript node `[104]`.**  A target-complete compression of a Type A
certificate's support onto a smaller proper baseline-preserving atom realizes
the registered target on the ambient object.

`certificate.common.uncompressible` is `cor:uncompressible`: the smaller proper
atom already realizes the target.  `complete` is the exit's own
target-completeness clause, which carries that realization back to `object`. -/
theorem target_of_targetCompleteSubsupport
    {presentation : TypeAB.Presentation.{u}} {object : FiniteObject.{u}}
    (certificate : TypeAB.TypeACertificate presentation object)
    {smaller : Finset object.Vertex}
    (nonempty : smaller.Nonempty)
    (proper : smaller ⊂ certificate.common.support)
    (baseline : TypeAB.Baseline presentation (object.induce smaller))
    (complete : presentation.Target (object.induce smaller) →
      presentation.Target object) :
    presentation.Target object :=
  complete (certificate.common.uncompressible smaller nonempty proper baseline)

/-! ## `lem:typeA-exits-discharged`, manuscript nodes `[96]`, `[98]`, `[100]`,
`[104]`, `[106]`

`Graph.ReceiverExhaustion.Exit` already carries the manuscript's eight saturated
receiver exits of `def:typeA-saturated-exits` on six constructors, so no new exit
carrier is introduced here:

* `rootedReturn` is exit (1), the Mersenne anchored return;
* `twoPath` is exit (2), two returns through one port whose lengths sum to an
  accepted cycle length;
* `closed` covers exits (3), (5) and (6) -- the `P₁₃` label collision, the
  target-complete compression against `cor:uncompressible`, and the
  delocalization alternatives -- each of which the manuscript discharges by
  producing the target outright;
* `peel` is exit (4), `handoff` is exit (7), `residual` is exit (8).

The three theorems below turn the closing constructors into the registered
target.  They consume the interface's own equivalences and add no graph fact. -/

section Exits

open Hypostructure.Graph.ReceiverExhaustion

universe uAmbient uBranch uData uVertex

variable {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
variable {CycleLengthOK : Nat → Prop}

/-- **Exit (1), manuscript node `[96]`.**  An anchored return of accepted length
through a completion port is an edge-rooted return, hence the dyadic cycle
target, by `RootedReturnTargetAlgebra.target_iff_hasRootedReturn`.  This is
`lem:return-equivalence` read through the registered interface. -/
theorem target_of_rootedReturn
    {interface :
      ReceiverExhaustion.TargetInterface.{uAmbient, uBranch, uVertex}
        P T CycleLengthOK}
    {input : Core.Strategy.ProblemInput P}
    (certificate :
      interface.rootedReturn.RootedReturn (interface.object input)) :
    T.Predicate input.object :=
  (interface.target_iff_cycle input).mpr
    ((interface.rootedReturn.target_iff_hasRootedReturn
      (interface.object input)).mpr ⟨certificate⟩)

/-- **Exit (2), manuscript node `[98]`.**  Two internally disjoint anchored
returns through one completion port glue into a single cycle whose length is the
sum of theirs, so an accepted sum is the target.  This is
`lem:typeA-common-port-return-cycle`; the gluing itself is
`CommonEndpointsCycle.target`. -/
theorem target_of_commonEndpointsCycle
    {interface :
      ReceiverExhaustion.TargetInterface.{uAmbient, uBranch, uVertex}
        P T CycleLengthOK}
    {input : Core.Strategy.ProblemInput P}
    (pair : Graph.CommonEndpointsCycle (interface.object input))
    (accepted :
      CycleLengthOK (pair.forward.length + pair.backward.length)) :
    T.Predicate input.object :=
  (interface.target_iff_cycle input).mpr
    ⟨pair.target CycleLengthOK accepted⟩

/-- **`lem:typeA-exits-discharged`.**  On a branch where exit (4) has already
been peeled away, exit (7) already handed off, and exit (8) already routed --
that is, where the peel, handoff and residual families are uninhabited -- every
remaining exit produces the registered target.

This is the exhaustiveness statement the closing nodes of Figure 8 consume: the
manuscript's "exits (1)--(3), (5) and (6) are closed exits". -/
theorem target_of_exit
    {interface :
      ReceiverExhaustion.TargetInterface.{uAmbient, uBranch, uVertex}
        P T CycleLengthOK}
    {input : Core.Strategy.ProblemInput P}
    (exit : Exit interface (fun _ => PEmpty.{uData + 1})
      (fun _ => PEmpty.{uData + 1}) (fun _ => PEmpty.{uData + 1}) input) :
    T.Predicate input.object := by
  cases exit with
  | rootedReturn certificate => exact target_of_rootedReturn certificate
  | twoPath pair accepted => exact target_of_commonEndpointsCycle pair accepted
  | closed hit => exact hit
  | peel step => exact step.elim
  | handoff entry => exact entry.elim
  | residual entry => exact entry.elim

end Exits

end Hypostructure.Graph.TypeAReceiverClosure
