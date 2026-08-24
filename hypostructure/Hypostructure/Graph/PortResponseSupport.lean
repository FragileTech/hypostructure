import Hypostructure.Graph.SparsePortActivation
import Hypostructure.Graph.FinitePathSelection
import Hypostructure.Graph.SameTokenRoutingGerms

/-!
# The canonical response support of a selected surplus port

`lem:sparse-port-activation`'s `Γ(p)`, and the canonical paths it is built from.

> For every selected port `p = (h,x) ∈ 𝒫_exc`, there is a canonical finite
> response support `Γ(p)` with the following properties.  (a) The port support
> is `T(p) = {x, a_p, b_p}`.  (b) There is a simple `x`--`h` path
> `R_p ⊆ G − hx`.  Its first edge after `x` is either `xa_p` or `xb_p`.
> (c) If `p` is open, then `Γ(p)` contains the lexicographically first path
> `Q_p ⊆ G − x` supplied by `lem:single-open-port-suppression-witness`; this
> path joins `a_p` to `b_p` and has length `2^{j(p)} − 1` for some `j(p) ≥ 2`.
> (d) If `p` is triangular, then `Γ(p)` contains the triangle `x a_p b_p x` and
> the lexicographically first return path `R_p` from (b).
>
> The construction of `Γ(p)` uses only `G`, the ordered vertex labels, and the
> port `p`; hence it is canonical.

Clause (a) is `SurplusPort.support`, and clause (b)'s existence is
`portReturn_of_minimal`; both are already carried.  What this module adds is
`Γ(p)` itself: the *canonical* choice the manuscript's "lexicographically first"
names, and the two-case support the construction records.

The choice is `Graph.FinitePathSelection.select?`, the framework's own
length-major path schedule -- "lexicographically first" is exactly the head of
that schedule.  It is total, returning `none` when no path exists, so `Γ(p)` is
a function of `G` and the port alone, which is the canonicity the lemma claims.
At a selected minimal counterexample the two selections are `some`, because the
existence clauses `portReturn_of_minimal` and `openPortWitness_of_minimal`
supply a path; that is `returnSelection_isSome` and `suppressionSelection_isSome`
below.

The two cases are recorded exactly as the manuscript records them: the open port
contributes `Q_p`, and the triangular port contributes the triangle together
with `R_p`.  Nothing else is added to `Γ(p)`; in particular the open case does
not record `R_p`, because widening `Γ(p)` would widen clause (a) of
`def:surplus-blockers` and so change which pairs are blocked.
-/

namespace Hypostructure.Graph

universe u

namespace FiniteObject.SurplusPort

variable {object : FiniteObject.{u}} {threshold : Nat}

/-- The ambient object with the port's own edge `c(p)x(p)` removed: the graph
`G − hx` that clause (b)'s return path runs in. -/
noncomputable def deletedPortGraph (port : SurplusPort object threshold) :
    SimpleGraph object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact object.graph.deleteEdges {s(port.centre, port.endpoint)}

instance decidableDeletedPortAdj (port : SurplusPort object threshold) :
    DecidableRel port.deletedPortGraph.Adj := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  unfold deletedPortGraph
  infer_instance

/-- **The canonical return path `R_p`.**  The lexicographically first simple
`x(p)`--`c(p)` path of `G − c(p)x(p)`, as the framework's own length-major
schedule selects it.

The hypothesis is the ledger fact itself.  Clause (b) is committed as
`Nonempty (PortReturn …)`, and `SimpleGraph.Reachable` is by definition
`Nonempty (Walk …)`, so the existence of the canonical choice needs the
*proposition* and not a chosen witness.  There is nothing to assume: if no
return path existed the port's edge would be a bridge, and
`EdgeContraction.hasReturn_of_minimal` has already refuted that at a selected
minimal counterexample. -/
noncomputable def canonicalReturn
    (port : SurplusPort object threshold) {left right : object.Vertex}
    (returns : Nonempty (PortReturn object port.centre port.endpoint left right)) :
    (by
      letI : FinEnum object.Vertex := object.vertices
      letI : Fintype object.Vertex := by infer_instance
      letI : DecidableEq object.Vertex := object.vertices.decEq
      exact FinitePathSelection.SelectedPath port.deletedPortGraph
        port.endpoint port.centre) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := by infer_instance
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact FinitePathSelection.selectOfReachable port.deletedPortGraph
    (returns.map (fun return' => return'.path))

/-- The vertices the canonical return path visits. -/
noncomputable def returnSupport
    (port : SurplusPort object threshold) {left right : object.Vertex}
    (returns : Nonempty (PortReturn object port.centre port.endpoint left right)) :
    Finset object.Vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := by infer_instance
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact (port.canonicalReturn returns).path.1.support.toFinset

/-- The selected endpoint is the initial vertex of its canonical return and
therefore belongs to `R_p`. -/
theorem endpoint_mem_returnSupport
    (port : SurplusPort object threshold) {left right : object.Vertex}
    (returns : Nonempty (PortReturn object port.centre port.endpoint left right)) :
    port.endpoint ∈ port.returnSupport returns := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := by infer_instance
  letI : DecidableEq object.Vertex := object.vertices.decEq
  simp [returnSupport]

/-- The canonical return support is connected because it is the support of the
canonical simple return path already carried by the active demand. -/
theorem connectedOn_returnSupport
    (port : SurplusPort object threshold) {left right : object.Vertex}
    (returns : Nonempty (PortReturn object port.centre port.endpoint left right)) :
    SupportComponents.Connected.ConnectedOn object
      (port.returnSupport returns) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := by infer_instance
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  let deletedWalk := (port.canonicalReturn returns).path.1
  let inclusion : port.deletedPortGraph →g object.graph :=
    .ofLE (by
      unfold deletedPortGraph
      exact object.graph.deleteEdges_le {s(port.centre, port.endpoint)})
  let ambientWalk : object.graph.Walk port.endpoint port.centre :=
    deletedWalk.map inclusion
  have supportEq : ambientWalk.support = deletedWalk.support := by
    rw [show ambientWalk.support = deletedWalk.support.map inclusion from by
      exact SimpleGraph.Walk.support_map inclusion deletedWalk]
    simp [inclusion]
  rw [returnSupport, ← supportEq]
  exact SameTokenRoutingGerms.connectedOn_walkSupport ambientWalk

/-- **`Γ(p)`, the canonical response support.**

Clause (d) at a triangular port: the triangle `x a_p b_p x` -- whose vertices are
exactly `T(p)` -- together with the return path `R_p`.  Clause (c) at an open
port: the suppression path `Q_p ⊆ G − x(p)`.

Both hypotheses are the facts node `[128]` commits, so `Γ(p)` is a function of
the object and the port: neither the return nor the suppression path is a
parameter to be supplied, and neither can fail to exist -- clause (b) is
`lem:bridgeless` and clause (c) is the open-port suppression witness, both
already proved at a selected minimal counterexample. -/
noncomputable def responseSupport {LengthOK : Nat → Prop}
    (port : SurplusPort object threshold) {left right : object.Vertex}
    (returns : Nonempty (PortReturn object port.centre port.endpoint left right))
    (suppresses : ¬ object.graph.Adj left right →
      Nonempty (OpenPortWitness object LengthOK port.endpoint left right)) :
    Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  exact if adjacent : object.graph.Adj left right then
      port.support ∪ port.returnSupport returns
    else
      ((suppresses adjacent).some.path.support).toFinset

/-- **Clause (d).**  At a triangular port `Γ(p)` contains the triangle's
vertices, which are exactly `T(p)`. -/
theorem support_subset_responseSupport_of_triangular {LengthOK : Nat → Prop}
    (port : SurplusPort object threshold) {left right : object.Vertex}
    (returns : Nonempty (PortReturn object port.centre port.endpoint left right))
    (suppresses : ¬ object.graph.Adj left right →
      Nonempty (OpenPortWitness object LengthOK port.endpoint left right))
    (adjacent : object.graph.Adj left right) :
    port.support ⊆ port.responseSupport returns suppresses := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  unfold responseSupport
  rw [dif_pos adjacent]
  exact Finset.subset_union_left

/-- **Clause (d), second half.**  At a triangular port `Γ(p)` contains the
canonical return path `R_p`. -/
theorem returnSupport_subset_responseSupport_of_triangular {LengthOK : Nat → Prop}
    (port : SurplusPort object threshold) {left right : object.Vertex}
    (returns : Nonempty (PortReturn object port.centre port.endpoint left right))
    (suppresses : ¬ object.graph.Adj left right →
      Nonempty (OpenPortWitness object LengthOK port.endpoint left right))
    (adjacent : object.graph.Adj left right) :
    port.returnSupport returns ⊆ port.responseSupport returns suppresses := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  unfold responseSupport
  rw [dif_pos adjacent]
  exact Finset.subset_union_right

/-- **Clause (c).**  At an open port `Γ(p)` is the suppression path's own
support, and that path avoids `x(p)`, which is the manuscript's `Q_p ⊆ G − x`. -/
theorem responseSupport_of_open {LengthOK : Nat → Prop}
    (port : SurplusPort object threshold) {left right : object.Vertex}
    (returns : Nonempty (PortReturn object port.centre port.endpoint left right))
    (suppresses : ¬ object.graph.Adj left right →
      Nonempty (OpenPortWitness object LengthOK port.endpoint left right))
    (isOpen : ¬ object.graph.Adj left right) :
    port.endpoint ∉ port.responseSupport returns suppresses := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  unfold responseSupport
  rw [dif_neg isOpen]
  simpa using (suppresses isOpen).some.avoids_endpoint

/-- **`T(p) ∪ Γ(p)`**, the declared demand support that clause (a) of
`def:surplus-blockers` intersects. -/
noncomputable def declaredSupport {LengthOK : Nat → Prop}
    (port : SurplusPort object threshold) {left right : object.Vertex}
    (returns : Nonempty (PortReturn object port.centre port.endpoint left right))
    (suppresses : ¬ object.graph.Adj left right →
      Nonempty (OpenPortWitness object LengthOK port.endpoint left right)) :
    Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact port.support ∪ port.responseSupport returns suppresses

theorem support_subset_declaredSupport {LengthOK : Nat → Prop}
    (port : SurplusPort object threshold) {left right : object.Vertex}
    (returns : Nonempty (PortReturn object port.centre port.endpoint left right))
    (suppresses : ¬ object.graph.Adj left right →
      Nonempty (OpenPortWitness object LengthOK port.endpoint left right)) :
    port.support ⊆ port.declaredSupport returns suppresses := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  unfold declaredSupport
  exact Finset.subset_union_left

end FiniteObject.SurplusPort

end Hypostructure.Graph
