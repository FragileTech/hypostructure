import Hypostructure.Graph.Contraction
import Hypostructure.Graph.ExcessPortFamily
import Hypostructure.Graph.TightVertexSuppression
import Hypostructure.Graph.Contraction

/-!
# Port activation: the canonical response support `Γ(p)`

`lem:sparse-port-activation`.  A selected port `p = (c(p), x(p))` whose endpoint
carries exactly the shoulder pair `s(p) = {a_p, b_p}` is activated by the data
it carries in every case and the data its two cases supply.

Every selected port carries the return path `R_p ⊆ G − c(p)x(p)` of clause (b):
the port's own edge is not a bridge, because contracting it gives a strictly
smaller object still meeting the baseline -- the endpoint's degree and the
centre's surplus pay for the merged vertex -- so minimality supplies that
contraction an accepted cycle and avoidance turns it into the return.  Its
first edge after `x(p)` is a shoulder, since the only other incidence of the
endpoint is the deleted port edge.  Then:

* if `p` is *open* -- the shoulders are nonadjacent -- suppressing `x(p)` and
  joining its shoulders produces a strictly smaller object still meeting the
  baseline, so minimality gives it an accepted cycle; target avoidance forces
  that cycle through the inserted shoulder chord, and deleting the chord leaves
  a simple `a_p`--`b_p` path in `G − x(p)` whose *restored* length is accepted.
  For the manuscript's dyadic target that is its `Q_p` of length `2^{j}−1`;
  nothing here writes a length or a base.
* if `p` is *triangular* -- the shoulders are adjacent -- the triangle
  `x(p) a_p b_p x(p)` is present, and that is the whole of clause (d) beyond the
  return path.

The shoulder pair is a hypothesis, not an assumption about the baseline: at the
manuscript's `δ = 3` the endpoint has exactly `δ − 1 = 2` shoulders, which is
`SurplusPort.card_shoulders`, and a caller at another baseline gets a statement
about the ports that happen to carry a pair.  No numeral occurs here.

The contraction operation and its return theorem are `Contraction`'s, and the
suppression operation, its minimum-degree preservation and the cycle
reconstruction are all `TightVertexSuppression`'s; this module only reads a
surplus port as one of their configurations.
-/

namespace Hypostructure.Graph

universe u

namespace FiniteObject

namespace SurplusPort

variable {object : FiniteObject.{u}} {threshold : Nat}

/-- **`T(p) = {x(p)} ∪ s(p)`**, the declared demand support of a port. -/
noncomputable def support (port : SurplusPort object threshold) :
    Finset object.Vertex := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact insert port.endpoint port.shoulders

/-- A port is *open* when its two shoulders are nonadjacent, and *triangular*
when they are adjacent.  This is the manuscript's dichotomy at the shoulder
pair, and it is decidable on a finite object. -/
def Open (_port : SurplusPort object threshold)
    (left right : object.Vertex) : Prop :=
  ¬ object.graph.Adj left right

/-- **Clause (d): a triangular port carries the triangle `x a_p b_p x`.**

Nothing is constructed: the two shoulder edges are the endpoint's own
incidences and the third edge is the case hypothesis. -/
theorem triangle_of_shoulders_adj (port : SurplusPort object threshold)
    {left right : object.Vertex}
    (leftShoulder : left ∈ port.shoulders)
    (rightShoulder : right ∈ port.shoulders)
    (adjacent : object.graph.Adj left right) :
    object.graph.Adj port.endpoint left ∧ object.graph.Adj left right ∧
      object.graph.Adj right port.endpoint :=
  ⟨((port.mem_shoulders_iff left).1 leftShoulder).2, adjacent,
    (((port.mem_shoulders_iff right).1 rightShoulder).2).symm⟩

/-! ## Clause (b): the return path `R_p` -/

/-- **`R_p`: the manuscript's return path at one selected port.**

A simple path of the ambient object from the port's endpoint back to its centre
which does not use the port's own edge, and whose first edge after the endpoint
is one of the two shoulders. -/
structure PortReturn (object : FiniteObject.{u})
    (centre endpoint left right : object.Vertex) where
  /-- `R_p ⊆ G − c(p)x(p)`. -/
  path : (object.graph.deleteEdges {s(centre, endpoint)}).Walk endpoint centre
  /-- `R_p` is simple. -/
  isPath : path.IsPath
  /-- The first edge of `R_p` after `x(p)` is `x a_p` or `x b_p`. -/
  first_shoulder : path.snd = left ∨ path.snd = right

/-- **`lem:sparse-port-activation`, clause (b).**

The port's own edge is not a bridge: contracting it gives a strictly smaller
object which still meets the baseline, because the endpoint degree and the
centre's surplus together pay for the merged vertex, so minimality supplies that
contraction an accepted cycle and avoidance turns it into a return.  The first
edge of that return after the endpoint is a shoulder because the only other
incidence of the endpoint is the deleted port edge itself.

The hypotheses are the standing baseline, the selected object's own avoidance,
and its own minimality, together with the port's shoulder pair -- the same three
ledger facts clause (c) consumes. -/
theorem portReturn_of_minimal {LengthOK : Nat → Prop}
    (port : SurplusPort object threshold)
    {left right : object.Vertex}
    (shoulders : ∀ vertex : object.Vertex,
      vertex ∈ port.shoulders ↔ (vertex = left ∨ vertex = right))
    (baseline : threshold ≤ object.minDegree)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimal : ∀ smaller : FiniteObject.{u},
      smaller.LexicographicallySmaller object →
      threshold ≤ smaller.minDegree → HasCycleWithLength LengthOK smaller) :
    Nonempty (PortReturn object port.centre port.endpoint left right) := by
  classical
  let contraction : EdgeContraction object :=
    { tail := port.centre
      head := port.endpoint
      adjacent := port.adjacent }
  -- The endpoint pays the baseline and the centre pays one unit of surplus,
  -- which is exactly the cost of the merged vertex.
  have endpointPositive : 0 < object.degree port.endpoint := by
    letI : FinEnum object.Vertex := object.vertices
    letI : DecidableRel object.graph.Adj := object.decideAdj
    change 0 < object.graph.degree port.endpoint
    exact SimpleGraph.Adj.degree_pos_left port.adjacent.symm
  have endpointBaseline : threshold ≤ object.degree port.endpoint :=
    le_trans baseline (object.minDegree_le_degree port.endpoint)
  have degreeSum : threshold + 2 ≤
      object.degree contraction.tail + object.degree contraction.head := by
    have centreHigh := port.centre_high
    change threshold + 2 ≤
      object.degree port.centre + object.degree port.endpoint
    omega
  obtain ⟨⟨forward, forwardPath⟩⟩ :=
    contraction.hasReturn_of_minimal (LengthOK := LengthOK) degreeSum baseline
      avoids minimal
  -- Read the return from the endpoint, where its first edge is a shoulder.
  let path := forward.reverse
  have notNil : ¬ path.Nil :=
    SimpleGraph.Walk.not_nil_of_ne
      (fun equality => port.adjacent.ne equality.symm)
  have firstAdj : contraction.severed.Adj port.endpoint path.snd :=
    path.adj_snd notNil
  obtain ⟨adjacent, different⟩ := contraction.severed_adj.mp firstAdj
  have notCentre : path.snd ≠ port.centre := by
    intro equality
    rw [equality] at different
    exact different Sym2.eq_swap
  exact ⟨{
    path := path
    isPath := forwardPath.reverse
    first_shoulder :=
      shoulders path.snd |>.1
        ((port.mem_shoulders_iff path.snd).2 ⟨notCentre, adjacent⟩) }⟩

/-- **The port, read as a suppression configuration.**

The endpoint is the suppressed vertex, the port's centre is the configuration's
centre, and the two shoulders are its left and right.  Every field is read off
the port: the endpoint's incidences are exactly its centre and its shoulders,
which is what `mem_shoulders_iff` says. -/
noncomputable def configuration (port : SurplusPort object threshold)
    {left right : object.Vertex}
    (shoulders : ∀ vertex : object.Vertex,
      vertex ∈ port.shoulders ↔ (vertex = left ∨ vertex = right))
    (distinct : left ≠ right) (openPort : port.Open left right) :
    TightVertexSuppression.Configuration object := by
  classical
  have leftShoulder : left ∈ port.shoulders := (shoulders left).2 (Or.inl rfl)
  have rightShoulder : right ∈ port.shoulders :=
    (shoulders right).2 (Or.inr rfl)
  exact
    { vertex := port.endpoint
      center := port.centre
      left := left
      right := right
      vertex_center := port.adjacent.symm
      vertex_left := ((port.mem_shoulders_iff left).1 leftShoulder).2
      vertex_right := ((port.mem_shoulders_iff right).1 rightShoulder).2
      neighbors := by
        intro other adjacent
        by_cases centre : other = port.centre
        · exact Or.inl centre
        · rcases (shoulders other).1
              ((port.mem_shoulders_iff other).2 ⟨centre, adjacent⟩) with
            equality | equality
          · exact Or.inr (Or.inl equality)
          · exact Or.inr (Or.inr equality)
      center_ne_left :=
        fun equality =>
          ((port.mem_shoulders_iff left).1 leftShoulder).1 equality.symm
      center_ne_right :=
        fun equality =>
          ((port.mem_shoulders_iff right).1 rightShoulder).1 equality.symm
      left_ne_right := distinct
      shoulder_missing := openPort }

/-- **`Q_p`: the manuscript's suppression witness at one open port.**

A simple path of the ambient object joining the two shoulders, avoiding the
port's endpoint, and whose length restored by one is an accepted cycle length.
The manuscript reads this as `2^{j(p)} − 1` with `j(p) ≥ 2`; the accepted set is
a parameter here, so the statement is its own. -/
structure OpenPortWitness (object : FiniteObject.{u}) (LengthOK : Nat → Prop)
    (endpoint left right : object.Vertex) where
  /-- The path `Q_p ⊆ G − x(p)`. -/
  path : object.graph.Walk left right
  /-- `Q_p` is simple. -/
  isPath : path.IsPath
  /-- `Q_p ⊆ G − x(p)`: the suppressed endpoint is not on it. -/
  avoids_endpoint : endpoint ∉ path.support
  /-- The restored length is accepted, which is the manuscript's `2^{j(p)}`. -/
  restored_length_ok : LengthOK (path.length + 1)

/-- A simple path of `G − x` with accepted restored length, read in the ambient
object along the canonical vertex-deletion embedding.  The image walk has the
same length and the same support, none of whose vertices is the deleted one. -/
theorem openPortWitness_of_deleted {LengthOK : Nat → Prop}
    {endpoint : object.Vertex}
    {left right : (object.deleteVertex endpoint).Vertex}
    (path : (object.deleteVertex endpoint).graph.Walk left right)
    (isPath : path.IsPath) (lengthOK : LengthOK (path.length + 1)) :
    Nonempty (OpenPortWitness object LengthOK endpoint left.1 right.1) := by
  let embedding := object.deleteVertexEmbedding endpoint
  have images : (path.map embedding.toHom).support =
      path.support.map embedding.toHom :=
    SimpleGraph.Walk.support_map (f := embedding.toHom) (p := path)
  have avoids : endpoint ∉ (path.map embedding.toHom).support := by
    rw [images]
    intro member
    obtain ⟨vertex, _, image⟩ := List.mem_map.1 member
    exact @Finset.ne_of_mem_erase object.Vertex object.vertices.decEq
      object.vertexFinset endpoint vertex.1 vertex.2 image
  have lengths : (path.map embedding.toHom).length = path.length :=
    SimpleGraph.Walk.length_map (f := embedding.toHom) (p := path)
  exact ⟨{
    path := path.map embedding.toHom
    isPath :=
      SimpleGraph.Walk.map_isPath_of_injective embedding.injective isPath
    avoids_endpoint := avoids
    restored_length_ok := lengths ▸ lengthOK }⟩

/-- **`lem:sparse-port-activation`, clause (c).**

An open selected port is activated: minimality of the object supplies an
accepted cycle in the suppressed object, avoidance forces it through the
inserted shoulder chord, and the reconstruction returns `Q_p`.

The hypotheses are the standing baseline, the selected object's own avoidance,
and its own minimality -- the three things the ledger already carries at this
branch -- together with the port's shoulder pair. -/
theorem openPortWitness_of_minimal {LengthOK : Nat → Prop}
    (port : SurplusPort object threshold)
    {left right : object.Vertex}
    (shoulders : ∀ vertex : object.Vertex,
      vertex ∈ port.shoulders ↔ (vertex = left ∨ vertex = right))
    (distinct : left ≠ right) (openPort : port.Open left right)
    (baseline : threshold ≤ object.minDegree)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimal : ∀ smaller : FiniteObject.{u},
      smaller.LexicographicallySmaller object →
      threshold ≤ smaller.minDegree → HasCycleWithLength LengthOK smaller) :
    Nonempty (OpenPortWitness object LengthOK port.endpoint left right) := by
  classical
  let configuration := port.configuration shoulders distinct openPort
  obtain ⟨_, ⟨reconstructed⟩⟩ :=
    configuration.singleSuppressionWitness_of_minimal (LengthOK := LengthOK)
      baseline avoids minimal port.centre_high
  -- The reconstructed path lives in `G − x(p)`; read it in the ambient object.
  exact openPortWitness_of_deleted (endpoint := port.endpoint)
    reconstructed.path reconstructed.isPath reconstructed.restored_length_ok

end SurplusPort

end FiniteObject

end Hypostructure.Graph
