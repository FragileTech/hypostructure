import Hypostructure.Graph.BoundaryDemand
import Hypostructure.Graph.DeletionCriticality

/-!
# Surplus ports and the excess selector

`def:surplus-ports` and `lem:sparse-excess-port-extraction`, the objects the
sparse surplus branch is stated on.

Let `H = V_{>δ}(G)` be the vertices strictly above the registered baseline.  A
*surplus port* is an ordered edge `p = (h, x)` with `h ∈ H`; `h` is its high
centre and `x` its endpoint.  Node `[10]`'s independence of `H` forces `x` to
sit exactly at the baseline, so its neighbours other than `h` — the *shoulders*
of `p` — number exactly `δ - 1`.  For the manuscript's `δ = 3` that is the
shoulder pair `s(p) = {a_p, b_p}`, and nothing below writes either numeral: the
threshold is a parameter and the shoulder count is `δ - 1` at it.

The excess selector `𝒫_exc` takes, at each high centre, every incident port, so
a centre of degree `d` contributes `d - δ` of them.  Summing over the centres is
`σ(G)`, which is `lem:sparse-excess-port-extraction`'s count.

Nothing here is specialized to one manuscript: the baseline is a parameter and
no numeral occurs.
-/

namespace Hypostructure.Graph

universe u

namespace FiniteObject

variable (object : FiniteObject.{u}) (threshold : Nat)

/-- **`def:surplus-ports`.**  An ordered edge whose first endpoint is strictly
above the registered baseline. -/
structure SurplusPort where
  /-- `c(p)`, the high centre. -/
  centre : object.Vertex
  /-- `x(p)`, the endpoint the port is taken at. -/
  endpoint : object.Vertex
  /-- `h ∈ H = V_{>δ}(G)`. -/
  centre_high : threshold < object.degree centre
  /-- `x ∈ N_G(h)`. -/
  adjacent : object.graph.Adj centre endpoint

variable {object threshold}

namespace SurplusPort

/-- **The shoulders `N_G(x(p)) ∖ {c(p)}`.**  At `δ = 3` this is the manuscript's
shoulder pair `s(p) = {a_p, b_p}`. -/
noncomputable def shoulders (port : SurplusPort object threshold) :
    Finset object.Vertex := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact (object.orderedNeighbors port.endpoint).toFinset.erase port.centre

theorem mem_shoulders_iff (port : SurplusPort object threshold)
    (vertex : object.Vertex) :
    vertex ∈ port.shoulders ↔
      vertex ≠ port.centre ∧ object.graph.Adj port.endpoint vertex := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  simp [shoulders, FiniteObject.mem_orderedNeighbors_iff]

/-- **The endpoint of a surplus port sits exactly at the baseline.**

Node `[10]`'s `lem:deletion-critical` says the vertices strictly above the
baseline are pairwise nonadjacent, so the endpoint of a port cannot be one of
them; the baseline supplies the other inequality.  This is the manuscript's
*"By `lem:deletion-critical`, `H` is independent, so every neighbour of a vertex
in `H` has degree exactly `3`"*. -/
theorem endpoint_degree_eq (port : SurplusPort object threshold)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex)
    (independent : ∀ left right : object.Vertex,
      threshold < object.degree left → threshold < object.degree right →
      ¬ object.graph.Adj left right) :
    object.degree port.endpoint = threshold := by
  refine Nat.le_antisymm ?_ (baseline port.endpoint)
  by_contra above
  exact independent port.centre port.endpoint port.centre_high
    (Nat.lt_of_not_le above) port.adjacent

/-- **A port has exactly `δ - 1` shoulders.**  At the manuscript's `δ = 3` this
is the shoulder *pair*: `N_G(x) = {c(p), a_p, b_p}` with `a_p, b_p ≠ c(p)`
distinct. -/
theorem card_shoulders (port : SurplusPort object threshold)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex)
    (independent : ∀ left right : object.Vertex,
      threshold < object.degree left → threshold < object.degree right →
      ¬ object.graph.Adj left right) :
    port.shoulders.card = threshold - 1 := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have neighbours :
      (object.orderedNeighbors port.endpoint).toFinset =
        object.graph.neighborFinset port.endpoint := by
    ext vertex
    simp [FiniteObject.mem_orderedNeighbors_iff, SimpleGraph.mem_neighborFinset]
  have member : port.centre ∈ object.graph.neighborFinset port.endpoint := by
    simp [SimpleGraph.mem_neighborFinset, port.adjacent.symm]
  have degree := port.endpoint_degree_eq baseline independent
  have count : (object.graph.neighborFinset port.endpoint).card =
      object.degree port.endpoint := by
    rw [← object.orderedNeighbors_length port.endpoint,
      ← List.toFinset_card_of_nodup (object.orderedNeighbors_nodup port.endpoint),
      neighbours]
  rw [shoulders, neighbours, Finset.card_erase_of_mem member, count, degree]

end SurplusPort

end FiniteObject

end Hypostructure.Graph
