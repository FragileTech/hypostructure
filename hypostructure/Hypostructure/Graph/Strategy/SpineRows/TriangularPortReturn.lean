import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## `lem:triangular-port-return`

The port edge is restored to the return supplied by `lem:bridgeless`.  Its
first endpoint incidence is one of the two shoulders.  Target avoidance rules
out the two-edge shoulder route, so after discarding a possible triangular
shoulder edge the tail contains a noncentral completion incidence. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def triangularPortReturnRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.triangularPortReturn
    { Requires := [K .bridgeless, K .selection, K .highCentreNormalForm,
        K .triangularShoulderCompletion]
      Produces := [K .triangularPortReturn]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let bridgeless := (inputs.get (K .bridgeless)).down
      let selection := (inputs.get (K .selection)).down
      let normal := (inputs.get (K .highCentreNormalForm)).down
      let completion := (inputs.get (K .triangularShoulderCompletion)).down
      .cons (key := K .triangularPortReturn) ⟨by
        change TriangularPortReturnStatement data inputs.current.object
        classical
        intro centre centreHeavy endpoint endpointMem
        obtain ⟨left, right, leftShoulder, rightShoulder, leftNeRight,
          leftRight, completes, notBothCentral, centralCompletion⟩ :=
            completion centre centreHeavy endpoint endpointMem
        have centreEndpoint :=
          (Graph.mem_triangularEndpoints_iff.mp endpointMem).1
        have centreHigh : Graph.IsHighCentre inputs.current.object
            data.threshold centre :=
          Nat.lt_trans (Nat.lt_succ_self data.threshold) centreHeavy
        have nf := normal centre centreHigh
        have endpointDegreeThree :
            inputs.current.object.degree endpoint = 3 := by
          rw [nf.neighbourTight centreEndpoint, data.threshold_eq_three]
        have neighbourCard (vertex : inputs.current.object.Vertex) :
            (inputs.current.object.orderedNeighbors vertex).toFinset.card =
              inputs.current.object.degree vertex := by
          rw [List.toFinset_card_of_nodup
            (inputs.current.object.orderedNeighbors_nodup vertex),
            inputs.current.object.orderedNeighbors_length vertex]
        have exhaustEndpoint (target : inputs.current.object.Vertex)
            (targetAdj : inputs.current.object.graph.Adj endpoint target) :
            target = centre ∨ target = left ∨ target = right := by
          by_contra distinct
          push_neg at distinct
          rcases distinct with ⟨targetCentre, targetLeft, targetRight⟩
          have subset : ({centre, left, right, target} :
              Finset inputs.current.object.Vertex) ⊆
              (inputs.current.object.orderedNeighbors endpoint).toFinset := by
            intro item itemMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at itemMem
            rcases itemMem with rfl | rfl | rfl | rfl
            · simpa [inputs.current.object.mem_orderedNeighbors_iff] using
                centreEndpoint.symm
            · simpa [inputs.current.object.mem_orderedNeighbors_iff] using
                leftShoulder.1
            · simpa [inputs.current.object.mem_orderedNeighbors_iff] using
                rightShoulder.1
            · simpa [inputs.current.object.mem_orderedNeighbors_iff] using targetAdj
          have four : 4 ≤ ({centre, left, right, target} :
              Finset inputs.current.object.Vertex).card := by
            simp [leftShoulder.2, rightShoulder.2, leftNeRight,
              targetCentre, targetLeft, targetRight,
              leftShoulder.2.symm, rightShoulder.2.symm, leftNeRight.symm,
              targetCentre.symm, targetLeft.symm, targetRight.symm]
          have bound := Finset.card_le_card subset
          rw [neighbourCard, endpointDegreeThree] at bound
          omega
        let contraction : Graph.EdgeContraction inputs.current.object :=
          { tail := centre
            head := endpoint
            adjacent := centreEndpoint }
        obtain ⟨forward, forwardPath⟩ := bridgeless contraction
        let path := forward.reverse
        have pathNotNil : ¬ path.Nil :=
          SimpleGraph.Walk.not_nil_of_ne (fun equality =>
            contraction.adjacent.ne equality.symm)
        have firstAdjSevered : contraction.severed.Adj endpoint path.snd :=
          path.adj_snd pathNotNil
        obtain ⟨firstAdj, firstNotPort⟩ :=
          contraction.severed_adj.mp firstAdjSevered
        have firstNotCentre : path.snd ≠ centre := by
          intro equality
          rw [equality] at firstNotPort
          exact firstNotPort Sym2.eq_swap
        have firstShoulder : path.snd = left ∨ path.snd = right := by
          rcases exhaustEndpoint path.snd firstAdj with centreCase | result
          · exact (firstNotCentre centreCase).elim
          · exact result
        let return' : Graph.FiniteObject.SurplusPort.PortReturn
            inputs.current.object centre endpoint left right :=
          { path := path
            isPath := forwardPath.reverse
            first_shoulder := firstShoulder }
        refine ⟨left, right, leftShoulder, rightShoulder, leftNeRight,
          return', ?_, ?_, ?_⟩
        · change endpoint ∉ path.tail.support
          have nodup : path.support.Nodup := forwardPath.reverse.support_nodup
          rw [← path.cons_support_tail pathNotNil] at nodup
          intro member
          exact (List.pairwise_cons.mp nodup).1 endpoint member rfl
        · intro accepted
          let certificate : Graph.EdgeRootedReturn inputs.current.object
              Graph.EdgeRootedReturn.AnyLength :=
            { dart := ⟨(centre, endpoint), centreEndpoint⟩
              path := path
              isPath := forwardPath.reverse
              length_ok := trivial }
          apply selection.1
          exact ⟨{
            vertex := centre
            walk := certificate.cycle
            isCycle := certificate.cycle_isCycle
            length_ok := by
              rw [certificate.cycle_length]
              exact accepted }⟩
        · intro notCentralEdge
          let shoulder := path.snd
          let q := path.tail
          have qNotNil : ¬ q.Nil := by
            exact SimpleGraph.Walk.not_nil_of_ne firstNotCentre
          have qPath : q.IsPath := forwardPath.reverse.tail
          have firstQAdjSevered : contraction.severed.Adj shoulder q.snd :=
            q.adj_snd qNotNil
          have firstQAdj : inputs.current.object.graph.Adj shoulder q.snd :=
            (contraction.severed_adj.mp firstQAdjSevered).1
          have firstQEdge : s(shoulder, q.snd) ∈ q.edges := by
            change s(path.snd, q.snd) ∈ q.edges
            rw [← q.cons_tail_eq qNotNil, SimpleGraph.Walk.edges_cons]
            simp
          have endpointAvoids : endpoint ∉ q.support := by
            have nodup : path.support.Nodup := forwardPath.reverse.support_nodup
            rw [← path.cons_support_tail pathNotNil] at nodup
            intro member
            exact (List.pairwise_cons.mp nodup).1 endpoint
              (by simpa [q] using member) rfl
          have qSndNotEndpoint : q.snd ≠ endpoint := by
            intro equality
            apply endpointAvoids
            rw [← equality]
            exact List.mem_of_mem_tail (q.snd_mem_tail_support qNotNil)
          have shoulderCases : shoulder = left ∨ shoulder = right :=
            firstShoulder
          rcases shoulderCases with shoulderLeft | shoulderRight
          · have shoulderEq : shoulder = left := shoulderLeft
            by_cases targetRight : q.snd = right
            · let q2 := q.tail
              have q2NotNil : ¬ q2.Nil := by
                apply SimpleGraph.Walk.not_nil_of_ne
                simpa [q2, targetRight] using rightShoulder.2
              have q2AdjSevered : contraction.severed.Adj right q2.snd := by
                simpa [q2, targetRight] using q2.adj_snd q2NotNil
              have q2Adj := (contraction.severed_adj.mp q2AdjSevered).1
              have q2Edge : s(right, q2.snd) ∈ q2.edges := by
                have generic : s(q.snd, q2.snd) ∈ q2.edges := by
                  rw [← q2.cons_tail_eq q2NotNil, SimpleGraph.Walk.edges_cons]
                  simp
                simpa [targetRight] using generic
              have q2EdgeQ : s(right, q2.snd) ∈ q.edges := by
                have tailEdge : s(right, q2.snd) ∈ q.tail.edges := by
                  simpa [q2] using q2Edge
                generalize q2.snd = target at tailEdge ⊢
                rw [← q.cons_tail_eq qNotNil, SimpleGraph.Walk.edges_cons,
                  List.mem_cons]
                exact Or.inr tailEdge
              have q2NotEndpoint : q2.snd ≠ endpoint := by
                intro equality
                apply endpointAvoids
                rw [← q.cons_support_tail qNotNil]
                exact List.mem_cons_of_mem _ (by
                  simpa [q2, equality] using
                    List.mem_of_mem_tail (q2.snd_mem_tail_support q2NotNil))
              have q2NotLeft : q2.snd ≠ left := by
                intro equality
                have nodup := qPath.support_nodup
                rw [← q.cons_support_tail qNotNil] at nodup
                exact (List.pairwise_cons.mp nodup).1 q2.snd (by
                  simpa [q2] using
                    List.mem_of_mem_tail (q2.snd_mem_tail_support q2NotNil))
                  (by simpa [shoulderEq, equality])
              have q2NotRight : q2.snd ≠ right := q2Adj.ne.symm
              have q2NotCentre : q2.snd ≠ centre := by
                intro equality
                have q2Path : q2.IsPath := qPath.tail
                have q2One : q2.length = 1 := by
                  apply q2Path.length_eq_one_of_mem_edges
                  simpa [q2, targetRight, equality] using q2Edge
                have qLength : q.length = 2 := by
                  have := q.length_tail_add_one qNotNil
                  simpa [q2, q2One] using this.symm
                have pathLength : path.length = 3 := by
                  have := path.length_tail_add_one pathNotNil
                  simpa [q, qLength] using this.symm
                apply (show ¬ data.LengthOK (path.length + 1) from by
                  intro accepted
                  apply selection.1
                  let certificate : Graph.EdgeRootedReturn
                      inputs.current.object Graph.EdgeRootedReturn.AnyLength :=
                    { dart := ⟨(centre, endpoint), centreEndpoint⟩
                      path := path
                      isPath := forwardPath.reverse
                      length_ok := trivial }
                  exact ⟨{
                    vertex := centre
                    walk := certificate.cycle
                    isCycle := certificate.cycle_isCycle
                    length_ok := by
                      rw [certificate.cycle_length]
                      exact accepted }⟩)
                rw [pathLength]
                rw [data.lengthOK_iff_powerOfTwo]
                exact ⟨⟨2, by norm_num⟩, by norm_num, by norm_num⟩
              exact ⟨right, q2.snd, Or.inr rfl, q2Adj, q2NotEndpoint,
                q2NotLeft, q2NotRight, q2NotCentre, q2EdgeQ⟩
            · have targetLeft : q.snd ≠ left := by
                simpa [shoulderEq] using firstQAdj.ne.symm
              have targetCentre : q.snd ≠ centre := by
                intro equality
                apply notCentralEdge
                apply qPath.length_eq_one_of_mem_edges
                simpa [equality] using firstQEdge
              exact ⟨left, q.snd, Or.inl rfl, by simpa [shoulderEq] using firstQAdj,
                qSndNotEndpoint, targetLeft, targetRight, targetCentre,
                by change s(left, q.snd) ∈ q.edges
                   simpa [shoulderEq] using firstQEdge⟩
          · have shoulderEq : shoulder = right := shoulderRight
            by_cases targetLeft : q.snd = left
            · let q2 := q.tail
              have q2NotNil : ¬ q2.Nil := by
                apply SimpleGraph.Walk.not_nil_of_ne
                simpa [q2, targetLeft] using leftShoulder.2
              have q2AdjSevered : contraction.severed.Adj left q2.snd := by
                simpa [q2, targetLeft] using q2.adj_snd q2NotNil
              have q2Adj := (contraction.severed_adj.mp q2AdjSevered).1
              have q2Edge : s(left, q2.snd) ∈ q2.edges := by
                have generic : s(q.snd, q2.snd) ∈ q2.edges := by
                  rw [← q2.cons_tail_eq q2NotNil, SimpleGraph.Walk.edges_cons]
                  simp
                simpa [targetLeft] using generic
              have q2EdgeQ : s(left, q2.snd) ∈ q.edges := by
                have tailEdge : s(left, q2.snd) ∈ q.tail.edges := by
                  simpa [q2] using q2Edge
                generalize q2.snd = target at tailEdge ⊢
                rw [← q.cons_tail_eq qNotNil, SimpleGraph.Walk.edges_cons,
                  List.mem_cons]
                exact Or.inr tailEdge
              have q2NotEndpoint : q2.snd ≠ endpoint := by
                intro equality
                apply endpointAvoids
                rw [← q.cons_support_tail qNotNil]
                exact List.mem_cons_of_mem _ (by
                  simpa [q2, equality] using
                    List.mem_of_mem_tail (q2.snd_mem_tail_support q2NotNil))
              have q2NotRight : q2.snd ≠ right := by
                intro equality
                have nodup := qPath.support_nodup
                rw [← q.cons_support_tail qNotNil] at nodup
                exact (List.pairwise_cons.mp nodup).1 q2.snd (by
                  simpa [q2] using
                    List.mem_of_mem_tail (q2.snd_mem_tail_support q2NotNil))
                  (by simpa [shoulderEq, equality])
              have q2NotLeft : q2.snd ≠ left := q2Adj.ne.symm
              have q2NotCentre : q2.snd ≠ centre := by
                intro equality
                have q2One : q2.length = 1 := by
                  apply qPath.tail.length_eq_one_of_mem_edges
                  simpa [q2, targetLeft, equality] using q2Edge
                have qLength : q.length = 2 := by
                  have := q.length_tail_add_one qNotNil
                  simpa [q2, q2One] using this.symm
                have pathLength : path.length = 3 := by
                  have := path.length_tail_add_one pathNotNil
                  simpa [q, qLength] using this.symm
                have power : data.LengthOK (path.length + 1) := by
                  rw [pathLength, data.lengthOK_iff_powerOfTwo]
                  exact ⟨⟨2, by norm_num⟩, by norm_num, by norm_num⟩
                exact (show ¬ data.LengthOK (path.length + 1) from by
                  intro accepted
                  apply selection.1
                  let certificate : Graph.EdgeRootedReturn
                      inputs.current.object Graph.EdgeRootedReturn.AnyLength :=
                    { dart := ⟨(centre, endpoint), centreEndpoint⟩
                      path := path
                      isPath := forwardPath.reverse
                      length_ok := trivial }
                  exact ⟨{
                    vertex := centre
                    walk := certificate.cycle
                    isCycle := certificate.cycle_isCycle
                    length_ok := by
                      rw [certificate.cycle_length]
                      exact accepted }⟩) power
              exact ⟨left, q2.snd, Or.inl rfl, q2Adj, q2NotEndpoint,
                q2NotLeft, q2NotRight, q2NotCentre, q2EdgeQ⟩
            · have targetRight : q.snd ≠ right := by
                simpa [shoulderEq] using firstQAdj.ne.symm
              have targetCentre : q.snd ≠ centre := by
                intro equality
                apply notCentralEdge
                apply qPath.length_eq_one_of_mem_edges
                simpa [equality] using firstQEdge
              exact ⟨right, q.snd, Or.inr rfl, by simpa [shoulderEq] using firstQAdj,
                qSndNotEndpoint, targetLeft, targetRight, targetCentre,
                by change s(right, q.snd) ∈ q.edges
                   simpa [shoulderEq] using firstQEdge⟩⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
