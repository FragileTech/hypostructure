import Hypostructure.Graph.VisibleReceiverEntry
import Hypostructure.Graph.Contraction

/-!
# `lem:typeA-port-return`: every completion port has an anchored return

> Every completion port of a Type A support has at least one anchored return.
>
> *Proof.*  A completion port is an oriented edge of `G`.  By
> `lem:bridgeless`, the underlying edge lies on a cycle in `G`.  Removing the
> port edge from that cycle leaves a simple return path in the required
> orientation.

`lem:bridgeless` is already the framework's:
`Graph.EdgeContraction.hasReturn_of_minimal` says a minimal object avoiding the
cycle target has a simple return for every ordered edge whose two endpoint
degrees pay for the contraction, and its `HasReturn` is a simple path from the
tail back to the head in the graph with that edge deleted.  A completion port
`⃗e = (w,h)` is exactly such an ordered edge read from `h` to `w`, so the
return it produces is an anchored return through the port, verbatim.

The degree side condition is discharged from the baseline: two vertices of an
object of minimum degree `δ ≥ 2` have degree sum at least `δ + 2`.  Nothing
here reads a support, a scale, or a numeral; the baseline, the accepted-length
predicate and the minimality are all parameters, and the avoidance and
minimality arrive as the two halves of the selection statement rather than as
assumptions about this port.
-/

namespace Hypostructure.Graph.VisibleEntry

open Hypostructure

universe u v

variable {object : FiniteObject.{u}}

/-! ## From a severed return to an anchored return

`EdgeContraction.HasReturn` lives in `object.graph.deleteEdges {wh}`; an
anchored return lives in `object.graph` and records the avoidance as a property
of its edge list.  The two carry the same walk. -/

/-- **A severed return through a port is an anchored return through it.**  The
path is transferred back to the ambient graph unchanged, and the port edge is
absent from its edges because the severed graph does not have it. -/
noncomputable def anchoredReturnOfSeveredPath {receiver outside : object.Vertex}
    (adjacent : object.graph.Adj receiver outside)
    (path :
      (⟨outside, receiver, adjacent.symm⟩ :
        Graph.EdgeContraction object).severed.Path outside receiver) :
    AnchoredReturn object receiver outside := by
  classical
  set contraction : Graph.EdgeContraction object :=
    ⟨outside, receiver, adjacent.symm⟩ with contractionDef
  -- Every edge of a walk lies in its own graph's edge set, and the severed
  -- graph is the ambient one with the port edge removed.
  have inSevered : ∀ edge ∈ path.1.edges, edge ∈ contraction.severed.edgeSet :=
    path.1.edges_subset_edgeSet
  have inAmbient : ∀ edge ∈ path.1.edges, edge ∈ object.graph.edgeSet := by
    intro edge member
    induction edge using Sym2.ind with
    | _ left right =>
      exact ((Graph.EdgeContraction.severed_adj contraction).mp
        (inSevered _ member)).1
  refine
    { path := path.1.transfer object.graph inAmbient
      isPath := path.2.transfer inAmbient
      avoidsPort := ?_ }
  rw [SimpleGraph.Walk.edges_transfer]
  intro member
  -- The severed graph deleted exactly `s(h,w) = s(w,h)`, so it cannot occur.
  have := (Graph.EdgeContraction.severed_adj contraction).mp
    (inSevered _ member)
  exact this.2 (by rw [Sym2.eq_swap])

/-! ## The lemma -/

/-- **`lem:typeA-port-return`.**  A completion port of a receiver of an object
that is a minimal counterexample carries an anchored return.

The two hypotheses `avoids` and `minimal` are the two halves of the selection
statement nodes `[1]`--`[4]` committed; the baseline is the standing one.  The
port itself enters only through the adjacency `w ~ h` that makes it a port. -/
theorem exists_anchoredReturn {LengthOK : Nat → Prop} {threshold : Nat}
    {receiver outside : object.Vertex}
    (adjacent : object.graph.Adj receiver outside)
    (two_le : 2 ≤ threshold)
    (baseline : Graph.MinimumDegreeAtLeast threshold object)
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object)
    (minimal : ∀ smaller : FiniteObject.{u},
      smaller.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast threshold smaller →
      Graph.HasCycleWithLength LengthOK smaller) :
    Nonempty (AnchoredReturn object receiver outside) := by
  classical
  set contraction : Graph.EdgeContraction object :=
    ⟨outside, receiver, adjacent.symm⟩ with contractionDef
  -- Both endpoints meet the baseline, so their degree sum pays for the merge.
  have degreeSum : threshold + 2 ≤
      object.degree contraction.tail + object.degree contraction.head := by
    have left : threshold ≤ object.degree contraction.tail :=
      le_trans baseline (object.minDegree_le_degree contraction.tail)
    have right : threshold ≤ object.degree contraction.head :=
      le_trans baseline (object.minDegree_le_degree contraction.head)
    omega
  obtain ⟨path⟩ :=
    contraction.hasReturn_of_minimal (LengthOK := LengthOK) degreeSum baseline
      avoids minimal
  exact ⟨anchoredReturnOfSeveredPath adjacent path⟩

/-- **Every completion port has an anchored return**, at one object.  The
caller supplies the support, receiver, and port, so a residual-local executor
can instantiate the result on its selected support without naming a port. -/
theorem exists_anchoredReturn_of_mem_completionPorts {LengthOK : Nat → Prop}
    {threshold : Nat} (two_le : 2 ≤ threshold)
    (baseline : Graph.MinimumDegreeAtLeast threshold object)
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object)
    (minimal : ∀ smaller : FiniteObject.{u},
      smaller.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast threshold smaller →
      Graph.HasCycleWithLength LengthOK smaller)
    (support : Finset object.Vertex) (receiver outside : object.Vertex)
    (port : outside ∈ completionPorts object support receiver) :
    Nonempty (AnchoredReturn object receiver outside) :=
  exists_anchoredReturn (LengthOK := LengthOK) (mem_completionPorts.mp port).1
    two_le baseline avoids minimal

end Hypostructure.Graph.VisibleEntry
