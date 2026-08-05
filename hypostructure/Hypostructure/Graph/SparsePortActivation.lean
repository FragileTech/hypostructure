import Hypostructure.Graph.ExcessPortFamily
import Hypostructure.Graph.TightVertexSuppression

/-!
# Port activation: the canonical response support `Γ(p)`

`lem:sparse-port-activation`.  A selected port `p = (c(p), x(p))` whose endpoint
carries exactly the shoulder pair `s(p) = {a_p, b_p}` is activated by the data
its two cases supply:

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

The suppression operation, its minimum-degree preservation, and the cycle
reconstruction are all `TightVertexSuppression`'s; this module only reads a
surplus port as one of its configurations.
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
def Open (port : SurplusPort object threshold) (left right : object.Vertex) :
    Prop := ¬ object.graph.Adj left right

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
