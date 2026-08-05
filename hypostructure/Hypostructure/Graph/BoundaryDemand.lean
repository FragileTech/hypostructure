import Hypostructure.Graph.WindowRemainder

/-!
# Positive deficiency and the boundary-incidence supply

`def:deficiency-surplus` measures external degree demand by *positive
deficiency* rather than signed charge: a vertex of internal degree below the
baseline needs that many incidences leaving its region, and a high-degree
neighbour cannot cancel the need.

Everything here is a sum of vertex-local counts, which is how the manuscript
argues.  `internalDegree` is the number of neighbours a vertex has inside a
support; the ambient degree minus it is the number that leave.  No edge set is
ever manipulated, so nothing has to be transported through an induced-subgraph
isomorphism.

The baseline is a parameter.  Nothing here knows the manuscript's value for it,
and the `3` of `def:deficiency-surplus` never appears.
-/

namespace Hypostructure.Graph

open Hypostructure
open scoped BigOperators

universe u

namespace FiniteObject

/-- The number of neighbours a vertex has inside a support. -/
noncomputable def internalDegree (object : FiniteObject.{u})
    (support : Finset object.Vertex) (vertex : object.Vertex) : Nat := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  exact ((object.graph.neighborFinset vertex) ∩ support).card

/-- A vertex has no more neighbours inside a support than it has overall. -/
theorem internalDegree_le_degree (object : FiniteObject.{u})
    (support : Finset object.Vertex) (vertex : object.Vertex) :
    object.internalDegree support vertex ≤ object.degree vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  simpa [internalDegree, FiniteObject.degree] using
    Finset.card_le_card
      (Finset.inter_subset_left (s₁ := object.graph.neighborFinset vertex)
        (s₂ := support))

/-- Enlarging the support cannot lose an internal neighbour. -/
theorem internalDegree_mono (object : FiniteObject.{u})
    {small large : Finset object.Vertex} (contained : small ⊆ large)
    (vertex : object.Vertex) :
    object.internalDegree small vertex ≤
      object.internalDegree large vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  exact Finset.card_le_card (Finset.inter_subset_inter_left contained)

/-- **`def:deficiency-surplus`.**  `def⁺(X) = Σ_{v∈X} max{0, δ − d_X(v)}`, with
truncated subtraction supplying the `max`. -/
noncomputable def positiveDeficiency (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat) : Nat :=
  ∑ vertex ∈ support, (threshold - object.internalDegree support vertex)

/-- **`def:window-remainder-surplus-split`.**  The ambient surplus carried by
the vertices of a support, `Σ_{v} max{0, d_G(v) − δ}`. -/
noncomputable def ambientSurplus (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat) : Nat :=
  ∑ vertex ∈ support, (object.degree vertex - threshold)

/-- `e(X, G − X)`: the incidences leaving a support, counted from inside it. -/
noncomputable def boundaryIncidence (object : FiniteObject.{u})
    (support : Finset object.Vertex) : Nat :=
  ∑ vertex ∈ support,
    (object.degree vertex - object.internalDegree support vertex)

/-- **`lem:surplus-aware-window-stub`, first inequality.**
`def⁺(R) ≤ e(R, W)`.

The manuscript's argument verbatim: on the standing baseline every vertex of
the remainder already has ambient degree at least `δ`, so it is deficient
*inside* the remainder only because some of its incidences leave.  Writing
`d_G(v) = d_R(v) + e_v` gives `max{0, δ − d_R(v)} ≤ e_v` pointwise, and summing
over the remainder gives the claim.

No near-cubic hypothesis is used, exactly as the manuscript notes. -/
theorem positiveDeficiency_le_boundaryIncidence (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    object.positiveDeficiency support threshold ≤
      object.boundaryIncidence support :=
  Finset.sum_le_sum fun vertex _ =>
    Nat.sub_le_sub_right (baseline vertex) _

/-- The degree sum over a support splits into its baseline part and its
surplus: `Σ_{v∈X} d_G(v) = δ·|X| + σ(X)`.  This is the `39p₁₃ + σ_W` of
`lem:exact-window-join-identity` with the numerals left to the caller. -/
theorem sum_degree_eq_threshold_mul_card_add_ambientSurplus
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    ∑ vertex ∈ support, object.degree vertex =
      threshold * support.card + object.ambientSurplus support threshold := by
  classical
  have expand : ∑ vertex ∈ support, object.degree vertex =
      ∑ vertex ∈ support, ((object.degree vertex - threshold) + threshold) :=
    Finset.sum_congr rfl fun vertex _ =>
      (Nat.sub_add_cancel (baseline vertex)).symm
  rw [expand, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
    ambientSurplus, Nat.mul_comm]
  omega

/-- The boundary incidence of a support is its degree sum minus its internal
degree sum.  Truncated subtraction distributes because a vertex never has more
internal neighbours than neighbours. -/
theorem boundaryIncidence_eq_sub (object : FiniteObject.{u})
    (support : Finset object.Vertex) :
    object.boundaryIncidence support =
      (∑ vertex ∈ support, object.degree vertex) -
        ∑ vertex ∈ support, object.internalDegree support vertex := by
  classical
  rw [boundaryIncidence, Finset.sum_tsub_distrib]
  intro vertex _
  exact object.internalDegree_le_degree support vertex

/-- **`lem:surplus-aware-window-stub`, capacity half, in its reduced form.**

`e(W, R) ≤ δ·|W| + σ_W − (internal degree mass of the packing)`.

Read at the packed windows this is the manuscript's
`e(R,W) ≤ 15p₁₃ + σ_W`: the degree sum over `W` is `δ|W| + σ_W`, and every
incidence that stays inside a window is one that does not leave.  The
manuscript evaluates the internal mass as `2(order − 1)` per window -- twice
the path edges of an induced copy -- and `δ|W| = δ·order·p₁₃`, giving
`(δ·order − 2(order − 1))·p₁₃ + σ_W`, which at the registered presentation is
`15p₁₃ + σ_W`.  Neither numeral appears here. -/
theorem boundaryIncidence_le_of_internal_mass (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold internalMass : Nat)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex)
    (mass : internalMass ≤
      ∑ vertex ∈ support, object.internalDegree support vertex) :
    object.boundaryIncidence support ≤
      threshold * support.card + object.ambientSurplus support threshold -
        internalMass := by
  rw [object.boundaryIncidence_eq_sub support,
    object.sum_degree_eq_threshold_mul_card_add_ambientSurplus support threshold
      baseline]
  exact Nat.sub_le_sub_left mass _

end FiniteObject

end Hypostructure.Graph
