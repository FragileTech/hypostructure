import Hypostructure.Graph.PathChords
import Hypostructure.Graph.PortResponseSupport

/-!
# The declared support of a port is three vertices and one path (`[144a]`, G audit S144a)

Vocabulary-free.  A selected surplus port `p = (c, x)` of `G` has declared
support `T(p) ∪ Γ(p)` (`SurplusPort.declaredSupport`), and

* if `p` is triangular (the shoulders are adjacent), `Γ(p) = T(p) ∪ R_p` with
  `R_p` the canonical return: a **shortest** `x`–`c` path of `G − cx`, hence an
  induced path of `G − cx`;
* if `p` is open, `Γ(p)` is the support of a simple `a_p`–`b_p` path `Q_p` of
  `G − x` with `|Q_p| + 1` accepted.

So `declaredSupport p = T(p) ∪ P` with `T(p) = support p` and `P` the support of
one path of `G` (`PortPathSupport`), carrying its chord facts: on a graph
without an accepted cycle every chord of the path has an unaccepted span, a
triangular `R_p` has no chord at all, and every interior degree-`3` vertex has
exactly one edge off the path (its stub).
-/

namespace Hypostructure.Graph.PortPathCover

open Hypostructure
open Hypostructure.Graph

universe u

/-- **`P` is the support of a canonical port path of `G`** (with its chord facts). -/
def PortPathSupport (object : FiniteObject.{u}) (LengthOK : Nat → Prop)
    (P : Finset object.Vertex) : Prop := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact
    (∃ (x c : object.Vertex)
        (w : (object.graph.deleteEdges {s(c, x)}).Walk x c),
      object.graph.Adj c x ∧ w.IsPath ∧ P = w.support.toFinset ∧
        (∀ q : (object.graph.deleteEdges {s(c, x)}).Walk x c, q.IsPath →
          w.length ≤ q.length) ∧
        PathChords.ChordFree w ∧
        PathChords.ChordCycles LengthOK (w.mapLe (object.graph.deleteEdges_le _)) ∧
        PathChords.StubStructure (w.mapLe (object.graph.deleteEdges_le _))) ∨
    (∃ (x a b : object.Vertex) (w : object.graph.Walk a b),
      w.IsPath ∧ P = w.support.toFinset ∧ x ∉ w.support ∧ object.graph.Adj x a ∧
        object.graph.Adj x b ∧ ¬ object.graph.Adj a b ∧ LengthOK (w.length + 1) ∧
        PathChords.ChordCycles LengthOK w ∧ PathChords.StubStructure w)

theorem noCycle_form {LengthOK : Nat → Prop} {object : FiniteObject.{u}}
    (avoids : ¬ HasCycleWithLength LengthOK object) :
    ¬ ∃ (c : object.Vertex) (cy : object.graph.Walk c c), cy.IsCycle ∧ LengthOK cy.length :=
  fun ⟨c, cy, hc, ok⟩ => avoids ⟨⟨c, cy, hc, ok⟩⟩

section Port

variable {object : FiniteObject.{u}} {threshold : Nat}

open Graph.FiniteObject

/-- **The declared support of a port is its three-vertex support and one path.** -/
theorem declaredSupport_pathSupport {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (port : SurplusPort object threshold) {left right : object.Vertex}
    (returns : Nonempty (SurplusPort.PortReturn object port.centre port.endpoint left right))
    (suppresses : ¬ object.graph.Adj left right →
      Nonempty (SurplusPort.OpenPortWitness object LengthOK port.endpoint left right))
    (hl : object.graph.Adj port.endpoint left) (hr : object.graph.Adj port.endpoint right) :
    ∃ P, PortPathSupport object LengthOK P ∧
      port.declaredSupport returns suppresses =
        (by letI : DecidableEq object.Vertex := object.vertices.decEq; exact port.support ∪ P) := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have cyc := noCycle_form avoids
  by_cases adj : object.graph.Adj left right
  · refine ⟨port.returnSupport returns, Or.inl ?_, ?_⟩
    · letI : FinEnum object.Vertex := object.vertices
      letI : Fintype object.Vertex := by infer_instance
      let sel := port.canonicalReturn returns
      have hpath : sel.path.1.IsPath := sel.path.2
      have short : ∀ q : (object.graph.deleteEdges {s(port.centre, port.endpoint)}).Walk
          port.endpoint port.centre, q.IsPath → sel.path.1.length ≤ q.length := by
        intro q hq
        exact FinitePathSelection.selectOfReachable_length_le port.deletedPortGraph
          (returns.map (fun return' => return'.path)) ⟨q, hq⟩
      refine ⟨port.endpoint, port.centre, sel.path.1, port.adjacent, hpath, rfl, short,
        PathChords.chordFree_of_shortest _ hpath short, ?_, ?_⟩
      · exact PathChords.chordCycles_of_avoids _ (hpath.mapLe _) cyc
      · exact PathChords.stub_of_path _ (hpath.mapLe _)
    · unfold SurplusPort.declaredSupport SurplusPort.responseSupport
      rw [dif_pos adj]
      ext v
      simp
  · obtain ⟨Q⟩ := suppresses adj
    refine ⟨(suppresses adj).some.path.support.toFinset, Or.inr ?_, ?_⟩
    · refine ⟨port.endpoint, left, right, (suppresses adj).some.path,
        (suppresses adj).some.isPath, rfl, (suppresses adj).some.avoids_endpoint, hl, hr, adj,
        (suppresses adj).some.restored_length_ok,
        PathChords.chordCycles_of_avoids _ (suppresses adj).some.isPath cyc,
        PathChords.stub_of_path _ (suppresses adj).some.isPath⟩
    · unfold SurplusPort.declaredSupport SurplusPort.responseSupport
      rw [dif_neg adj]


end Port

/-! ## The port walk, with all its cycle facts -/

/-- **A canonical port walk of `G`**: a simple path with every chord/hub/closing
cycle fact, and its kind (a shortest return of `G − cx`, or an open suppression
path with a closing vertex `x` of its ends). -/
def PortWalk (object : FiniteObject.{u}) (LengthOK : Nat → Prop) {a b : object.Vertex}
    (w : object.graph.Walk a b) : Prop :=
  w.IsPath ∧ PathChords.ChordCycles LengthOK w ∧ PathChords.StubStructure w ∧
    PathChords.HubCycles LengthOK w ∧ PathChords.ClosedCycles LengthOK w ∧
    ((∃ wd : (object.graph.deleteEdges {s(b, a)}).Walk a b, object.graph.Adj b a ∧ wd.IsPath ∧
        w = wd.mapLe (object.graph.deleteEdges_le _) ∧
        ∀ q : (object.graph.deleteEdges {s(b, a)}).Walk a b, q.IsPath → wd.length ≤ q.length) ∨
      ∃ x, x ∉ w.support ∧ object.graph.Adj x a ∧ object.graph.Adj x b ∧
        ¬ object.graph.Adj a b ∧ LengthOK (w.length + 1))

section PortW

variable {object : FiniteObject.{u}} {threshold : Nat}

open Graph.FiniteObject

/-- **The declared support of a port is its support and one port walk.** -/
theorem declaredSupport_portWalk {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (port : SurplusPort object threshold) {left right : object.Vertex}
    (returns : Nonempty (SurplusPort.PortReturn object port.centre port.endpoint left right))
    (suppresses : ¬ object.graph.Adj left right →
      Nonempty (SurplusPort.OpenPortWitness object LengthOK port.endpoint left right))
    (hl : object.graph.Adj port.endpoint left) (hr : object.graph.Adj port.endpoint right) :
    ∃ (a b : object.Vertex) (w : object.graph.Walk a b), PortWalk object LengthOK w ∧
      port.declaredSupport returns suppresses =
        (by letI : DecidableEq object.Vertex := object.vertices.decEq
            exact port.support ∪ w.support.toFinset) := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have cyc := noCycle_form avoids
  by_cases adj : object.graph.Adj left right
  · letI : FinEnum object.Vertex := object.vertices
    letI : Fintype object.Vertex := by infer_instance
    let sel := port.canonicalReturn returns
    have hpath : sel.path.1.IsPath := sel.path.2
    have short : ∀ q : (object.graph.deleteEdges {s(port.centre, port.endpoint)}).Walk
        port.endpoint port.centre, q.IsPath → sel.path.1.length ≤ q.length := by
      intro q hq
      exact FinitePathSelection.selectOfReachable_length_le port.deletedPortGraph
        (returns.map (fun return' => return'.path)) ⟨q, hq⟩
    let w : object.graph.Walk port.endpoint port.centre :=
      sel.path.1.mapLe (object.graph.deleteEdges_le _)
    have hw : w.IsPath := hpath.mapLe _
    refine ⟨port.endpoint, port.centre, w, ⟨hw, PathChords.chordCycles_of_avoids _ hw cyc,
      PathChords.stub_of_path _ hw, PathChords.hubCycles_of_avoids _ hw cyc,
      PathChords.closedCycles_of_avoids _ hw cyc, Or.inl ⟨sel.path.1, port.adjacent, hpath, rfl,
        short⟩⟩, ?_⟩
    unfold SurplusPort.declaredSupport SurplusPort.responseSupport
    rw [dif_pos adj]
    ext v
    have : v ∈ w.support.toFinset ↔ v ∈ port.returnSupport returns := by
      simp [w, SurplusPort.returnSupport, SimpleGraph.Walk.support_mapLe_eq_support]
      first | done | exact Iff.rfl
    simp only [Finset.mem_union, this]
    tauto
  · obtain ⟨Q⟩ := suppresses adj
    refine ⟨left, right, (suppresses adj).some.path, ⟨(suppresses adj).some.isPath,
      PathChords.chordCycles_of_avoids _ (suppresses adj).some.isPath cyc,
      PathChords.stub_of_path _ (suppresses adj).some.isPath,
      PathChords.hubCycles_of_avoids _ (suppresses adj).some.isPath cyc,
      PathChords.closedCycles_of_avoids _ (suppresses adj).some.isPath cyc,
      Or.inr ⟨port.endpoint, (suppresses adj).some.avoids_endpoint, hl, hr, adj,
        (suppresses adj).some.restored_length_ok⟩⟩, ?_⟩
    unfold SurplusPort.declaredSupport SurplusPort.responseSupport
    rw [dif_neg adj]

end PortW

end Hypostructure.Graph.PortPathCover
