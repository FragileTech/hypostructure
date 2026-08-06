import Hypostructure.Graph.ReceiverRouting
import Hypostructure.Graph.NetCharge

/-!
# `lem:typeA-unsaturated-discharge`: the Type A discharging calculation

A Type A support carries no assigned surplus, so on the standing baseline every
one of its vertices spends at most the baseline inside it: the support splits
into *full* vertices, at internal degree exactly `δ`, and *receivers*, below it.
`lem:typeA-receiver-loads` sends every full vertex to exactly one receiver, and
`L(w)` counts the ones that arrive at `w`.

The manuscript's discharging is one line.  Measure a vertex by

  `ch(v) = (δ − d_X(v)) − α`,   `α = 1/s`,

so that `Σ_v ch(v) = defp(X) − |V(X)|/s`.  A full vertex has charge `−α` and is
assigned to one receiver; a receiver `w` starts at `q(w) − α` and pays `α` for
each of its `L(w)` arrivals.  If every receiver is unsaturated, `L(w) ≤ s·q(w) − 1`,
then

  `q(w) − α − α·L(w) ≥ q(w) − α − α(s·q(w) − 1) = 0`,

so the total is nonnegative and `defp(X) ≥ |V(X)|/s`.  At the manuscript's
`δ = 3`, `s = 4` the receiver capacities are `3, 7, 11` for internal degrees
`2, 1, 0`, which is its `n₃ ≤ 3n₂ + 7n₁ + 11n₀`.

Everything is carried at the scale `s`, so `α` never appears as a reciprocal and
the conclusion is the subtraction-free `NonNegativeNetCharge` of
`def:net-charge` at zero assigned surplus.  Nothing here is specialized to a
manuscript: the baseline and the scale are parameters and no numeral is written.
-/

namespace Hypostructure.Graph

open scoped BigOperators

universe u

namespace FiniteObject

open scoped Classical

variable {object : FiniteObject.{u}}

/-! ## The support splits into full vertices and receivers -/

/-- The full vertices of a support: those spending the whole baseline inside. -/
noncomputable def fullVertices (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat) :
    Finset object.Vertex := by
  classical
  exact support.filter fun vertex =>
    object.internalDegree support vertex = threshold

/-- The receivers of a support. -/
noncomputable def receivers (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat) :
    Finset object.Vertex := by
  classical
  exact support.filter fun vertex =>
    object.internalDegree support vertex < threshold

theorem mem_fullVertices {support : Finset object.Vertex} {threshold : Nat}
    {vertex : object.Vertex} :
    vertex ∈ object.fullVertices support threshold ↔
      vertex ∈ support ∧ object.internalDegree support vertex = threshold := by
  classical
  simp [fullVertices]

theorem mem_receivers {support : Finset object.Vertex} {threshold : Nat}
    {vertex : object.Vertex} :
    vertex ∈ object.receivers support threshold ↔
      object.IsReceiver support threshold vertex := by
  classical
  simp [receivers, IsReceiver]

/-- **A support of zero assigned surplus has no vertex above the baseline
inside it.**  Every vertex of it that is not full is a receiver, so the two
finsets are complementary in the support. -/
theorem receivers_eq_filter_not (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (capped : ∀ vertex ∈ support,
      object.internalDegree support vertex ≤ threshold) :
    object.receivers support threshold =
      support.filter (fun vertex =>
        ¬ object.internalDegree support vertex = threshold) := by
  classical
  ext vertex
  simp only [mem_receivers, IsReceiver, Finset.mem_filter]
  constructor
  · rintro ⟨inside, below⟩
    exact ⟨inside, by omega⟩
  · rintro ⟨inside, notFull⟩
    exact ⟨inside, lt_of_le_of_ne (capped vertex inside) notFull⟩

/-- **`|R| + |F| = |V(X)|`.** -/
theorem card_receivers_add_card_fullVertices (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (capped : ∀ vertex ∈ support,
      object.internalDegree support vertex ≤ threshold) :
    (object.receivers support threshold).card +
        (object.fullVertices support threshold).card = support.card := by
  classical
  rw [receivers_eq_filter_not object support threshold capped, fullVertices,
    Nat.add_comm]
  exact Finset.filter_card_add_filter_neg_card_eq_card
    (p := fun vertex => object.internalDegree support vertex = threshold)

/-! ## The routing partitions the full vertices -/

/-- **`Σ_w L(w) = |{full vertices}|`.**

The canonical routing is a function on the full vertices, so its fibres over the
receivers partition them.  This is `lem:typeA-receiver-loads`' only quantitative
consequence, and the only place the routing is counted. -/
theorem sum_routedLoad (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (routes : ∀ vertex ∈ support,
      object.internalDegree support vertex = threshold →
      ∃ receiver : object.Vertex,
        object.traceReceiver? support threshold vertex = some receiver ∧
          object.IsReceiver support threshold receiver) :
    ∑ receiver ∈ object.receivers support threshold,
        object.routedLoad support threshold receiver =
      (object.fullVertices support threshold).card := by
  classical
  have lands : ∀ vertex ∈ object.fullVertices support threshold,
      (object.traceReceiver? support threshold vertex).getD vertex ∈
        object.receivers support threshold := by
    intro vertex member
    obtain ⟨inside, full⟩ := mem_fullVertices.mp member
    obtain ⟨receiver, routed, isReceiver⟩ := routes vertex inside full
    rw [routed]
    exact mem_receivers.mpr isReceiver
  rw [Finset.card_eq_sum_card_fiberwise lands]
  refine Finset.sum_congr rfl fun receiver _ => ?_
  rw [routedLoad]
  refine congrArg Finset.card (Finset.ext fun vertex => ?_)
  constructor
  · intro member
    obtain ⟨inside, rest⟩ := Finset.mem_filter.mp member
    obtain ⟨atBaseline, routed⟩ := rest
    refine Finset.mem_filter.mpr
      ⟨mem_fullVertices.mpr ⟨inside, atBaseline⟩, ?_⟩
    rw [routed]
    rfl
  · intro member
    have isFull : vertex ∈ object.fullVertices support threshold :=
      Finset.mem_of_mem_filter _ member
    have landed :
        (object.traceReceiver? support threshold vertex).getD vertex = receiver :=
      (Finset.mem_filter.mp member).2
    obtain ⟨inside, atBaseline⟩ := mem_fullVertices.mp isFull
    obtain ⟨target, routed, _⟩ := routes vertex inside atBaseline
    refine Finset.mem_filter.mpr ⟨inside, atBaseline, ?_⟩
    rw [routed] at landed ⊢
    simpa using landed

/-! ## The discharging on a support with exceptional vertices

A Type B support is not a Type A support: its assigned high-degree centres sit
above the baseline, so the calculation below cannot be run on them.  What *can*
be run on them is the same calculation with the centres set aside, and that is
the generality the Type B bridge needs -- `def:typeB-assigned-ledger` measures a
centre by its own formula and every other vertex by the core formula.

Everything is the same argument as the plain case, which is recovered by taking
the exceptional set empty. -/

/-- **`L(w)` restricted to the non-exceptional full vertices.** -/
noncomputable def restrictedLoad (object : FiniteObject.{u})
    (support excluded : Finset object.Vertex) (threshold : Nat)
    (receiver : object.Vertex) : Nat := by
  classical
  exact ((support \ excluded).filter fun source =>
    object.internalDegree support source = threshold ∧
      object.traceReceiver? support threshold source = some receiver).card

/-- **`Σ_w L(w) = |{non-exceptional full vertices}|`**, with the routing
restricted to the non-exceptional vertices on both sides. -/
theorem sum_restrictedLoad (object : FiniteObject.{u})
    (support excluded : Finset object.Vertex) (threshold : Nat)
    (routes : ∀ vertex ∈ support \ excluded,
      object.internalDegree support vertex = threshold →
      ∃ receiver : object.Vertex,
        object.traceReceiver? support threshold vertex = some receiver ∧
          object.IsReceiver support threshold receiver ∧
            receiver ∉ excluded) :
    ∑ receiver ∈ object.receivers support threshold \ excluded,
        object.restrictedLoad support excluded threshold receiver =
      ((support \ excluded).filter fun vertex =>
        object.internalDegree support vertex = threshold).card := by
  classical
  have lands : ∀ vertex ∈ (support \ excluded).filter
      (fun vertex => object.internalDegree support vertex = threshold),
      (object.traceReceiver? support threshold vertex).getD vertex ∈
        object.receivers support threshold \ excluded := by
    intro vertex member
    obtain ⟨outside, full⟩ := Finset.mem_filter.mp member
    obtain ⟨receiver, routed, isReceiver, fresh⟩ := routes vertex outside full
    rw [routed]
    exact Finset.mem_sdiff.mpr ⟨mem_receivers.mpr isReceiver, fresh⟩
  rw [Finset.card_eq_sum_card_fiberwise lands]
  refine Finset.sum_congr rfl fun receiver _ => ?_
  rw [restrictedLoad]
  refine congrArg Finset.card (Finset.ext fun vertex => ?_)
  constructor
  · intro member
    obtain ⟨outside, rest⟩ := Finset.mem_filter.mp member
    obtain ⟨full, routed⟩ := rest
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨outside, full⟩, ?_⟩
    rw [routed]
    rfl
  · intro member
    obtain ⟨isFull, landed⟩ := Finset.mem_filter.mp member
    obtain ⟨outside, full⟩ := Finset.mem_filter.mp isFull
    obtain ⟨target, routed, _⟩ := routes vertex outside full
    refine Finset.mem_filter.mpr ⟨outside, full, ?_⟩
    rw [routed] at landed ⊢
    simpa using landed

/-- **A larger exceptional set counts fewer arrivals.**  `restrictedLoad` counts
the non-exceptional full vertices routed to a receiver, so enlarging the
exceptional set can only remove arrivals.  This is what lets one saturation
question serve two different post-ledger cores: the answer at the smaller core
implies the answer at the larger one. -/
theorem restrictedLoad_antitone (object : FiniteObject.{u})
    (support : Finset object.Vertex) {small large : Finset object.Vertex}
    (contained : small ⊆ large) (threshold : Nat) (receiver : object.Vertex) :
    object.restrictedLoad support large threshold receiver ≤
      object.restrictedLoad support small threshold receiver := by
  classical
  refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
  intro vertex member
  obtain ⟨inside, fresh⟩ := Finset.mem_sdiff.mp member
  exact Finset.mem_sdiff.mpr ⟨inside, fun present => fresh (contained present)⟩

/-- **The discharging calculation off an exceptional set.**

`Σ_{y ∉ H} ch(y) ≥ 0` on a support whose non-exceptional vertices are all at or
below the baseline, whose non-exceptional full vertices all route to
non-exceptional receivers, and whose non-exceptional receivers are all
unsaturated.  Written subtraction-free at the scale `s`. -/
theorem card_le_scaled_deficiency_off (object : FiniteObject.{u})
    (support excluded : Finset object.Vertex) (threshold scale : Nat)
    (capped : ∀ vertex ∈ support \ excluded,
      object.internalDegree support vertex ≤ threshold)
    (routes : ∀ vertex ∈ support \ excluded,
      object.internalDegree support vertex = threshold →
      ∃ receiver : object.Vertex,
        object.traceReceiver? support threshold vertex = some receiver ∧
          object.IsReceiver support threshold receiver ∧
            receiver ∉ excluded)
    (unsaturated : ∀ receiver ∈ object.receivers support threshold \ excluded,
      1 + object.restrictedLoad support excluded threshold receiver ≤
        scale * object.missingPorts support threshold receiver) :
    (support \ excluded).card ≤
      ∑ vertex ∈ support \ excluded,
        scale * (threshold - object.internalDegree support vertex) := by
  classical
  set rest := support \ excluded with restDef
  set full := rest.filter
    (fun vertex => object.internalDegree support vertex = threshold) with fullDef
  -- The receivers of the support outside the exceptional set are exactly the
  -- non-full vertices of `rest`.
  have receiversRest : object.receivers support threshold \ excluded =
      rest.filter
        (fun vertex => ¬ object.internalDegree support vertex = threshold) := by
    ext vertex
    simp only [Finset.mem_sdiff, mem_receivers, IsReceiver, Finset.mem_filter,
      restDef]
    constructor
    · rintro ⟨⟨inside, below⟩, fresh⟩
      exact ⟨⟨inside, fresh⟩, by omega⟩
    · rintro ⟨⟨inside, fresh⟩, notFull⟩
      exact ⟨⟨inside, lt_of_le_of_ne (capped vertex
        (Finset.mem_sdiff.mpr ⟨inside, fresh⟩)) notFull⟩, fresh⟩
  -- The full vertices contribute nothing to the deficiency.
  have deficiency : ∑ vertex ∈ rest,
      scale * (threshold - object.internalDegree support vertex) =
        ∑ receiver ∈ object.receivers support threshold \ excluded,
          scale * object.missingPorts support threshold receiver := by
    rw [← Finset.sum_filter_add_sum_filter_not rest
      (fun vertex => object.internalDegree support vertex = threshold)
      (fun vertex => scale * (threshold - object.internalDegree support vertex))]
    have vanishes : ∑ vertex ∈ full,
        scale * (threshold - object.internalDegree support vertex) = 0 := by
      refine Finset.sum_eq_zero fun vertex member => ?_
      rw [(Finset.mem_filter.mp member).2]
      simp
    rw [vanishes, Nat.zero_add, receiversRest]
    exact Finset.sum_congr rfl fun _ _ => rfl
  have paid : ∑ receiver ∈ object.receivers support threshold \ excluded,
      (1 + object.restrictedLoad support excluded threshold receiver) ≤
        ∑ receiver ∈ object.receivers support threshold \ excluded,
          scale * object.missingPorts support threshold receiver :=
    Finset.sum_le_sum unsaturated
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
    sum_restrictedLoad object support excluded threshold routes] at paid
  have fullEq : ((support \ excluded).filter
      (fun vertex => object.internalDegree support vertex = threshold)).card =
        full.card := rfl
  rw [fullEq] at paid
  have split : (object.receivers support threshold \ excluded).card +
      full.card = rest.card := by
    rw [receiversRest, fullDef, Nat.add_comm]
    exact Finset.filter_card_add_filter_neg_card_eq_card
      (p := fun vertex => object.internalDegree support vertex = threshold)
  rw [deficiency]
  omega

/-! ## `lem:typeA-unsaturated-discharge` -/

/-- **`lem:typeA-unsaturated-discharge`.**

A support of zero assigned surplus every receiver of which is unsaturated has
`defp(X) ≥ |V(X)|/s`, that is `No(X) ≥ 0`.

The three hypotheses are the manuscript's own: the surplus is zero, so no
internal degree exceeds the baseline; the canonical routing is total, which is
`lem:typeA-receiver-loads` and is node `[88]`'s committed fact; and every
receiver is unsaturated, which is node `[90]`'s.  The conclusion is stated in
the subtraction-free form `def:net-charge` compares, so nothing rounds. -/
theorem unsaturatedDischarge (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    (capped : ∀ vertex ∈ support,
      object.internalDegree support vertex ≤ threshold)
    (routes : ∀ vertex ∈ support,
      object.internalDegree support vertex = threshold →
      ∃ receiver : object.Vertex,
        object.traceReceiver? support threshold vertex = some receiver ∧
          object.IsReceiver support threshold receiver)
    (unsaturated : ∀ receiver : object.Vertex,
      object.IsReceiver support threshold receiver →
      1 + object.routedLoad support threshold receiver ≤
        scale * object.missingPorts support threshold receiver) :
    support.card ≤ scale * object.positiveDeficiency support threshold := by
  classical
  -- `s·defp(X)` is carried entirely by the receivers: a full vertex is exact.
  have deficiency : scale * object.positiveDeficiency support threshold =
      ∑ receiver ∈ object.receivers support threshold,
        scale * object.missingPorts support threshold receiver := by
    unfold FiniteObject.positiveDeficiency
    rw [Finset.mul_sum]
    rw [← Finset.sum_filter_add_sum_filter_not support
      (fun vertex => object.internalDegree support vertex = threshold)
      (fun vertex => scale * (threshold - object.internalDegree support vertex))]
    have vanishes : ∑ vertex ∈ support.filter
        (fun vertex => object.internalDegree support vertex = threshold),
        scale * (threshold - object.internalDegree support vertex) = 0 := by
      refine Finset.sum_eq_zero fun vertex member => ?_
      rw [(Finset.mem_filter.mp member).2]
      simp
    rw [vanishes, Nat.zero_add,
      ← receivers_eq_filter_not object support threshold capped]
    exact Finset.sum_congr rfl fun _ _ => rfl
  -- Each receiver pays for its own arrivals and for itself.
  have paid : ∑ receiver ∈ object.receivers support threshold,
      (1 + object.routedLoad support threshold receiver) ≤
        ∑ receiver ∈ object.receivers support threshold,
          scale * object.missingPorts support threshold receiver :=
    Finset.sum_le_sum fun receiver member =>
      unsaturated receiver (mem_receivers.mp member)
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
    sum_routedLoad object support threshold routes] at paid
  have split := card_receivers_add_card_fullVertices object support threshold capped
  rw [deficiency]
  omega

end FiniteObject

end Hypostructure.Graph
