import Hypostructure.Graph.ExcessPortFamily

/-!
# The primitive sparse blocker carrier `𝔘_sp(G)`

`def:primitive-sparse-blocker-carrier` builds

  `𝔘_sp(G) = V(G) ⊔ I_E(G) ⊔ 𝒫_exc`,  `I_E(G) = {(e,v) : e ∈ E(G), v ∈ e}`,

and `lem:primitive-carrier-supply` counts it:

  `|𝔘_sp(G)| = n + 2m + σ(G) ≤ 6n`.

The incidence family is the object's own ordered neighbour blocks -- the same
`centreBlocks` construction the excess selector is built from -- so its count is
`Σ_v d_G(v) = 2m` by the handshake, and the third summand is
`lem:sparse-excess-port-extraction`'s `σ(G)`.  The displayed bound `≤ 6n` is the
identity spent against the sparse upper envelope `m ≤ 2n − 2`, which is the
hypothesis the manuscript carries into this estimate; it is a hypothesis here
too, not an assumption about the object.

The baseline is a parameter and no numeral is written: the `6` of the display is
`4·2 − 2` at the envelope's own coefficients.
-/

namespace Hypostructure.Graph

universe u

namespace FiniteObject

variable (object : FiniteObject.{u}) (threshold : Nat)

/-- **`I_E(G)`**: the edge incidences, as ordered adjacent pairs `(v, w)` -- one
for each end of each edge. -/
noncomputable def incidences : Finset (object.Vertex × object.Vertex) :=
  object.centreBlocks object.orderedNeighbors

variable {object}

theorem mem_incidences_iff (pair : object.Vertex × object.Vertex) :
    pair ∈ object.incidences ↔ object.graph.Adj pair.1 pair.2 := by
  rw [incidences, mem_centreBlocks_iff]
  exact object.mem_orderedNeighbors_iff pair.1 pair.2

/-- **`|I_E(G)| = 2m`**: the handshake, read on the incidence family.  Each
vertex contributes its own degree, and the degree sum is twice the edge
count. -/
theorem card_incidences : object.incidences.card = 2 * object.edgeCount := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have blocks := card_centreBlocks (object := object) object.orderedNeighbors
    fun centre => object.orderedNeighbors_nodup centre
  have handshake :
      (∑ vertex : object.Vertex, object.degree vertex) =
        2 * object.edgeCount := by
    simpa [FiniteObject.degree, FiniteObject.edgeCount] using
      object.graph.sum_degrees_eq_twice_card_edges
  rw [incidences, blocks, ← handshake]
  exact Finset.sum_congr rfl fun vertex _ => object.orderedNeighbors_length vertex

variable (object)

/-- **`𝔘_sp(G) = V(G) ⊔ I_E(G) ⊔ 𝒫_exc`**, the primitive sparse blocker
carrier. -/
noncomputable def primitiveCarrier :
    Finset (object.Vertex ⊕ (object.Vertex × object.Vertex) ⊕
      (object.Vertex × object.Vertex)) :=
  object.vertexFinset.disjSum
    (object.incidences.disjSum (object.excessPorts threshold))

variable {object threshold}

/-- **`lem:primitive-carrier-supply`, the identity**: `|𝔘_sp(G)| = n + 2m + σ(G)`.

The three summands are disjoint by construction, so the count is the sum of the
three counts: the vertex count, the handshake, and
`lem:sparse-excess-port-extraction`. -/
theorem card_primitiveCarrier
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    (object.primitiveCarrier threshold).card =
      object.vertexCount + 2 * object.edgeCount +
        object.degreeSurplus threshold := by
  rw [primitiveCarrier, Finset.card_disjSum, Finset.card_disjSum,
    card_incidences, object.card_excessPorts baseline, object.card_vertexFinset,
    Nat.add_assoc]

/-- **`lem:primitive-carrier-supply`, the bound**: `|𝔘_sp(G)| ≤ 6n` on the
sparse upper envelope.

`n + 2m + σ(G) = 4m − (δ − 1)n` at the registered baseline, and the envelope
`m ≤ 2n − 2` turns that into `8n − 8 − 2n ≤ 6n`.  Both the envelope and the
baseline's `3 ≤ δ` are hypotheses; nothing about the object is assumed here. -/
theorem card_primitiveCarrier_le
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex)
    (three : 3 ≤ threshold)
    (handshake : threshold * object.vertexCount ≤ 2 * object.edgeCount)
    (envelope : object.edgeCount + 2 ≤ 2 * object.vertexCount) :
    (object.primitiveCarrier threshold).card ≤ 6 * object.vertexCount := by
  rw [card_primitiveCarrier baseline]
  have surplus : object.degreeSurplus threshold =
      2 * object.edgeCount - threshold * object.vertexCount := rfl
  have widened : 3 * object.vertexCount ≤ threshold * object.vertexCount :=
    Nat.mul_le_mul_right object.vertexCount three
  omega

end FiniteObject

end Hypostructure.Graph
