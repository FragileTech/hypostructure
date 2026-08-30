import Hypostructure.Graph.TwoTerminalClosure

/-! Generic one-edge closure facts used by the gadget-closure argument. -/

namespace Hypostructure.Graph.AddedEdgeClosure

open SimpleGraph
open scoped Sym2

universe u

/-- Every edge other than the newly inserted edge was already present. -/
theorem oldEdge_of_ne_added
    (object : FiniteObject.{u}) (left right : object.Vertex)
    (different : left ≠ right) {edge : Sym2 object.Vertex}
    (member : edge ∈ (object.addEdge left right).graph.edgeSet)
    (notAdded : edge ≠ s(left, right)) : edge ∈ object.graph.edgeSet := by
  change edge ∈ (object.graph ⊔ SimpleGraph.edge left right).edgeSet at member
  rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_edge_of_ne different] at member
  rcases member with old | added
  · exact old
  · exact (notAdded (Set.mem_singleton_iff.mp added)).elim

/-- Target avoidance forces an accepted cycle in a one-edge closure to use
the inserted edge. -/
theorem cycle_uses_addedEdge
    (object : FiniteObject.{u}) (left right : object.Vertex)
    (different : left ≠ right) {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (certificate : CycleCertificate (object.addEdge left right) LengthOK) :
    s(left, right) ∈ certificate.walk.edges := by
  by_contra omits
  have oldEdges : ∀ edge, edge ∈ certificate.walk.edges →
      edge ∈ object.graph.edgeSet := by
    intro edge member
    exact oldEdge_of_ne_added object left right different
      (certificate.walk.edges_subset_edgeSet member)
      (fun equality => omits (equality ▸ member))
  let oldWalk := certificate.walk.transfer object.graph oldEdges
  let oldCertificate : CycleCertificate object LengthOK := {
    vertex := certificate.vertex
    walk := oldWalk
    isCycle := certificate.isCycle.transfer oldEdges
    length_ok := by
      change LengthOK oldWalk.length
      rw [SimpleGraph.Walk.length_transfer]
      exact certificate.length_ok
  }
  exact avoids ⟨oldCertificate⟩

private theorem exists_orientedCycle
    (object : FiniteObject.{u}) (left right : object.Vertex)
    (different : left ≠ right) {start : object.Vertex}
    (cycle : (object.addEdge left right).graph.Walk start start)
    (isCycle : cycle.IsCycle) (uses : s(left, right) ∈ cycle.edges) :
    ∃ oriented : (object.addEdge left right).graph.Walk left left,
      oriented.IsCycle ∧ oriented.length = cycle.length ∧ oriented.snd = right := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have leftMember : left ∈ cycle.support :=
    cycle.fst_mem_support_of_mem_edges uses
  let forward := cycle.rotate left leftMember
  have forwardCycle : forward.IsCycle := isCycle.rotate leftMember
  have forwardUses : s(left, right) ∈ forward.edges :=
    (cycle.rotate_edges left leftMember).mem_iff.mpr uses
  have forwardLength : forward.length = cycle.length :=
    cycle.length_rotate left leftMember
  by_cases firstIsRight : forward.snd = right
  · exact ⟨forward, forwardCycle, forwardLength, firstIsRight⟩
  · have forwardNotNil : ¬ forward.Nil := forwardCycle.not_nil
    have rebuilt :
        (SimpleGraph.Walk.cons (forward.adj_snd forwardNotNil)
          forward.tail).IsCycle := by
      rw [forward.cons_tail_eq forwardNotNil]
      exact forwardCycle
    have tailData : forward.tail.IsPath ∧
        s(left, forward.snd) ∉ forward.tail.edges :=
      (SimpleGraph.Walk.cons_isCycle_iff forward.tail
        (forward.adj_snd forwardNotNil)).mp rebuilt
    have tailNotNil : ¬ forward.tail.Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      have cycleLength := forwardCycle.three_le_length
      have exactDrop := forward.length_tail_add_one forwardNotNil
      omega
    have tailUses : s(left, right) ∈ forward.tail.edges := by
      have split := forwardUses
      rw [← forward.cons_tail_eq forwardNotNil,
        SimpleGraph.Walk.edges_cons, List.mem_cons] at split
      rcases split with first | later
      · have rightIsSnd : right = forward.snd := by
          rw [Sym2.eq_iff] at first
          rcases first with same | reversed
          · exact same.2
          · exact (different reversed.2.symm).elim
        exact (firstIsRight rightIsSnd.symm).elim
      · exact later
    have rightIsPenultimate : right = forward.tail.penultimate :=
      tailData.1.eq_penultimate_of_mem_edges tailUses
    have forwardPenultimate : forward.penultimate = forward.tail.penultimate := by
      calc
        forward.penultimate =
            (SimpleGraph.Walk.cons (forward.adj_snd forwardNotNil)
              forward.tail).penultimate := by
                rw [forward.cons_tail_eq forwardNotNil]
        _ = forward.tail.penultimate :=
          SimpleGraph.Walk.penultimate_cons_of_not_nil
            (forward.adj_snd forwardNotNil) forward.tail tailNotNil
    have reverseSnd : forward.reverse.snd = right := by
      rw [SimpleGraph.Walk.snd_reverse, forwardPenultimate]
      exact rightIsPenultimate.symm
    exact ⟨forward.reverse, forwardCycle.reverse,
      by simpa only [SimpleGraph.Walk.length_reverse] using forwardLength,
      reverseSnd⟩

/-- The simple old-graph path obtained by removing the inserted edge from a
cycle in a one-edge extension. -/
structure ReconstructedPath
    (object : FiniteObject.{u}) (left right : object.Vertex)
    {LengthOK : Nat → Prop}
    (certificate : CycleCertificate (object.addEdge left right) LengthOK) where
  path : object.graph.Walk left right
  isPath : path.IsPath
  length_add_one : path.length + 1 = certificate.walk.length
  length_eq_predecessor : path.length = certificate.walk.length - 1
  restored_length_ok : LengthOK (path.length + 1)

noncomputable def reconstructPath
    {LengthOK : Nat → Prop} (object : FiniteObject.{u})
    (left right : object.Vertex) (different : left ≠ right)
    (certificate : CycleCertificate (object.addEdge left right) LengthOK)
    (uses : s(left, right) ∈ certificate.walk.edges) :
    ReconstructedPath object left right certificate := by
  classical
  have orientedExists := exists_orientedCycle object left right different
    certificate.walk certificate.isCycle uses
  let oriented := Classical.choose orientedExists
  have orientedData := Classical.choose_spec orientedExists
  have orientedCycle : oriented.IsCycle := orientedData.1
  have orientedLength : oriented.length = certificate.walk.length :=
    orientedData.2.1
  have orientedSnd : oriented.snd = right := orientedData.2.2
  have orientedNotNil : ¬ oriented.Nil := orientedCycle.not_nil
  have rebuilt :
      (SimpleGraph.Walk.cons (oriented.adj_snd orientedNotNil)
        oriented.tail).IsCycle := by
    rw [oriented.cons_tail_eq orientedNotNil]
    exact orientedCycle
  have tailData : oriented.tail.IsPath ∧
      s(left, oriented.snd) ∉ oriented.tail.edges :=
    (SimpleGraph.Walk.cons_isCycle_iff oriented.tail
      (oriented.adj_snd orientedNotNil)).mp rebuilt
  let returnWalk : (object.addEdge left right).graph.Walk right left :=
    oriented.tail.copy orientedSnd rfl
  let extensionPath : (object.addEdge left right).graph.Walk left right :=
    returnWalk.reverse
  have extensionPathIsPath : extensionPath.IsPath := by
    dsimp [extensionPath, returnWalk]
    exact (SimpleGraph.Walk.isPath_copy _ _ _).mpr tailData.1 |>.reverse
  have extensionPathAvoids : s(left, right) ∉ extensionPath.edges := by
    dsimp [extensionPath, returnWalk]
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse,
      SimpleGraph.Walk.edges_copy]
    simpa only [orientedSnd] using tailData.2
  have oldEdges : ∀ edge, edge ∈ extensionPath.edges →
      edge ∈ object.graph.edgeSet := by
    intro edge member
    exact oldEdge_of_ne_added object left right different
      (extensionPath.edges_subset_edgeSet member)
      (fun equality => extensionPathAvoids (equality ▸ member))
  let path := extensionPath.transfer object.graph oldEdges
  have pathIsPath : path.IsPath := extensionPathIsPath.transfer oldEdges
  have extensionLength : extensionPath.length + 1 = certificate.walk.length := by
    dsimp [extensionPath, returnWalk]
    rw [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_copy]
    have exactDrop := oriented.length_tail_add_one orientedNotNil
    omega
  have pathLength : path.length + 1 = certificate.walk.length := by
    dsimp [path]
    rw [SimpleGraph.Walk.length_transfer]
    exact extensionLength
  exact {
    path := path
    isPath := pathIsPath
    length_add_one := pathLength
    length_eq_predecessor := by omega
    restored_length_ok := by
      rw [pathLength]
      exact certificate.length_ok
  }

/-- Target avoidance supplies the edge-use proof needed for reconstruction. -/
noncomputable def reconstructPath_of_avoids
    {LengthOK : Nat → Prop} (object : FiniteObject.{u})
    (left right : object.Vertex) (different : left ≠ right)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (certificate : CycleCertificate (object.addEdge left right) LengthOK) :
    ReconstructedPath object left right certificate :=
  reconstructPath object left right different certificate
    (cycle_uses_addedEdge object left right different avoids certificate)

/-- Minimality applied after inserting the terminal edge gives the exact
Mersenne terminal path used in gadget-closure clauses (i) and (iii). -/
theorem terminalPath_of_minimal_addedEdge
    {LengthOK : Nat → Prop}
    (ambient object : FiniteObject.{u}) (left right : object.Vertex)
    (different : left ≠ right)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (smaller : (object.addEdge left right).LexicographicallySmaller ambient)
    (baseline : 3 ≤ (object.addEdge left right).minDegree)
    (minimal : ∀ candidate : FiniteObject.{u},
      candidate.LexicographicallySmaller ambient → 3 ≤ candidate.minDegree →
        HasCycleWithLength LengthOK candidate) :
    ∃ path : object.graph.Walk left right,
      path.IsPath ∧ LengthOK (path.length + 1) := by
  obtain ⟨certificate⟩ := minimal _ smaller baseline
  let reconstructed := reconstructPath_of_avoids object left right different
    avoids certificate
  exact ⟨reconstructed.path, reconstructed.isPath,
    reconstructed.restored_length_ok⟩

end Hypostructure.Graph.AddedEdgeClosure
