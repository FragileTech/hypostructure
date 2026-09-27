import Hypostructure.Graph.Contracts.TypeB.Support

/-!
# Contracts: triangular ports

`def:triangular-fan-core`, `lem:triangular-shoulder-completion`,
`lem:triangular-port-return`, `lem:triangular-first-landing` and
`lem:triangular-cross-shoulder`, each with every hypothesis explicit.
-/

namespace Hypostructure.Graph.Contracts.TypeB

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- `def:triangular-fan-core` at every heavy centre and nonempty family of
triangular ports. -/
theorem triangularFanCore
    (normal : HighCentreNormalFormStatement data object)
    (thresholdEq : data.threshold = 3) :
    TriangularFanCoreStatement data object := by
  intro centre centreHeavy ports portsNonempty triangular
  classical
  let shoulders : object.Vertex →
      Finset object.Vertex := fun endpoint =>
    (object.orderedNeighbors endpoint).toFinset.erase centre
  let core : Finset object.Vertex :=
    insert centre (ports ∪ ports.biUnion shoulders)
  let completion : object.Vertex →
      object.Vertex →
        object.Vertex → Prop :=
    fun endpoint shoulder target =>
      endpoint ∈ ports ∧ shoulder ∈ shoulders endpoint ∧
        object.graph.Adj shoulder target ∧
          target ≠ endpoint ∧ target ∉ shoulders endpoint
  let central : object.Vertex →
      object.Vertex →
        object.Vertex → Prop :=
    fun endpoint shoulder target =>
      completion endpoint shoulder target ∧ target = centre
  let crossTriangular : object.Vertex →
      object.Vertex →
        object.Vertex → Prop :=
    fun endpoint shoulder target =>
      completion endpoint shoulder target ∧
        ∃ other ∈ ports,
          other ≠ endpoint ∧ target ∈ shoulders other
  let outside : object.Vertex →
      object.Vertex →
        object.Vertex → Prop :=
    fun endpoint shoulder target =>
      completion endpoint shoulder target ∧ target ∉ core ∧
        ¬ object.graph.Adj centre target
  refine ⟨shoulders, core, completion, central, crossTriangular, outside,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro endpoint endpointMem
    have triangularMem := triangular endpointMem
    have centreEndpoint :=
      (Graph.mem_triangularEndpoints_iff.mp triangularMem).1
    have centreHigh : Graph.IsHighCentre object
        data.threshold centre := by
      exact Nat.lt_trans (Nat.lt_succ_self data.threshold) centreHeavy
    have endpointDegree :=
      (normal centre centreHigh).neighbourTight centreEndpoint
    have centreMember : centre ∈
        (object.orderedNeighbors endpoint).toFinset := by
      simpa [object.mem_orderedNeighbors_iff] using
        centreEndpoint.symm
    have neighbourCard :
        (object.orderedNeighbors endpoint).toFinset.card =
          object.degree endpoint := by
      rw [List.toFinset_card_of_nodup
        (object.orderedNeighbors_nodup endpoint),
        object.orderedNeighbors_length endpoint]
    refine ⟨?_, ?_, ?_⟩
    · intro vertex
      simp [shoulders, Graph.IsShoulder,
        object.mem_orderedNeighbors_iff, and_comm]
    · rw [show shoulders endpoint =
          (object.orderedNeighbors endpoint).toFinset.erase
            centre from rfl,
        Finset.card_erase_of_mem centreMember, neighbourCard,
        endpointDegree, thresholdEq]
    · obtain ⟨left, right, leftShoulder, rightShoulder, chord⟩ :=
        (Graph.mem_triangularEndpoints_iff.mp triangularMem).2
      refine ⟨left, right, ?_, ?_, chord.ne, chord⟩
      · simpa [shoulders, Graph.IsShoulder,
          object.mem_orderedNeighbors_iff, and_comm] using
          leftShoulder
      · simpa [shoulders, Graph.IsShoulder,
          object.mem_orderedNeighbors_iff, and_comm] using
          rightShoulder
  · intro vertex
    simp [core]
  · intro endpoint shoulder target
    rfl
  · intro endpoint shoulder target
    rfl
  · intro endpoint shoulder target
    rfl
  · intro endpoint shoulder target
    rfl


/-- `lem:triangular-shoulder-completion`. -/
theorem triangularShoulderCompletion
    (normal : HighCentreNormalFormStatement data object)
    (thresholdEq : data.threshold = 3)
    (three : 3 ≤ data.threshold)
    (baseline : data.threshold ≤ object.minDegree) :
    TriangularShoulderCompletionStatement data object := by
  classical
  intro centre centreHeavy endpoint endpointMem
  have centreEndpoint :=
    (Graph.mem_triangularEndpoints_iff.mp endpointMem).1
  have centreHigh : Graph.IsHighCentre object
      data.threshold centre :=
    Nat.lt_trans (Nat.lt_succ_self data.threshold) centreHeavy
  have nf := normal centre centreHigh
  obtain ⟨left, right, leftShoulder, rightShoulder, leftRight⟩ :=
    (Graph.mem_triangularEndpoints_iff.mp endpointMem).2
  have endpointDegree := nf.neighbourTight centreEndpoint
  have neighbourCard (vertex : object.Vertex) :
      (object.orderedNeighbors vertex).toFinset.card =
        object.degree vertex := by
    rw [List.toFinset_card_of_nodup
      (object.orderedNeighbors_nodup vertex),
      object.orderedNeighbors_length vertex]
  have thirdNeighbour (vertex first second : object.Vertex)
      (firstAdj : object.graph.Adj vertex first)
      (secondAdj : object.graph.Adj vertex second)
      (different : first ≠ second)
      (three : 3 ≤ object.degree vertex) :
      ∃ target, object.graph.Adj vertex target ∧
        target ≠ first ∧ target ≠ second := by
    by_contra absent
    push_neg at absent
    have subset :
        (object.orderedNeighbors vertex).toFinset ⊆
          {first, second} := by
      intro target targetMem
      have adjacent : object.graph.Adj vertex target := by
        simpa [object.mem_orderedNeighbors_iff] using targetMem
      rcases eq_or_ne target first with rfl | targetFirst
      · simp
      have targetSecond := absent target adjacent targetFirst
      simp [targetSecond]
    have bound := Finset.card_le_card subset
    rw [neighbourCard] at bound
    have pairCard : ({first, second} : Finset object.Vertex).card = 2 := by
      simp [different]
    rw [pairCard] at bound
    omega
  have exhaustThree (vertex first second third target :
      object.Vertex)
      (degreeThree : object.degree vertex = 3)
      (firstAdj : object.graph.Adj vertex first)
      (secondAdj : object.graph.Adj vertex second)
      (thirdAdj : object.graph.Adj vertex third)
      (firstSecond : first ≠ second) (firstThird : first ≠ third)
      (secondThird : second ≠ third)
      (targetAdj : object.graph.Adj vertex target) :
      target = first ∨ target = second ∨ target = third := by
    by_contra distinct
    push_neg at distinct
    rcases distinct with ⟨targetFirst, targetSecond, targetThird⟩
    have subset : ({first, second, third, target} :
        Finset object.Vertex) ⊆
        (object.orderedNeighbors vertex).toFinset := by
      intro item itemMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at itemMem
      rcases itemMem with rfl | rfl | rfl | rfl
      all_goals simpa [object.mem_orderedNeighbors_iff]
    have four : 4 ≤
        ({first, second, third, target} :
          Finset object.Vertex).card := by
      simp [targetFirst, targetSecond, targetThird, firstSecond,
        firstThird, secondThird, targetFirst.symm, targetSecond.symm,
        targetThird.symm, firstSecond.symm, firstThird.symm,
        secondThird.symm]
    have bound := Finset.card_le_card subset
    rw [neighbourCard, degreeThree] at bound
    omega
  have shoulderCompletion (shoulder other : object.Vertex)
      (shoulderData : Graph.IsShoulder object centre endpoint shoulder)
      (otherData : Graph.IsShoulder object centre endpoint other)
      (shoulderOther : object.graph.Adj shoulder other)
      (different : shoulder ≠ other) :
      ∃ target, object.graph.Adj shoulder target ∧
        target ≠ endpoint ∧ target ≠ shoulder ∧ target ≠ other := by
    have three : 3 ≤ object.degree shoulder :=
      le_trans three
        (le_trans baseline
          (object.minDegree_le_degree shoulder))
    obtain ⟨target, targetAdj, targetEndpoint, targetOther⟩ :=
      thirdNeighbour shoulder endpoint other shoulderData.1.symm shoulderOther
        otherData.1.ne three
    exact ⟨target, targetAdj, targetEndpoint, targetAdj.ne.symm, targetOther⟩
  refine ⟨left, right, leftShoulder, rightShoulder, leftRight.ne, leftRight,
    ?_, ?_, ?_, ?_⟩
  · intro shoulder shoulderCases
    rcases shoulderCases with shoulderEq | shoulderEq
    · subst shoulder
      simpa [leftRight.ne] using
        shoulderCompletion left right leftShoulder rightShoulder leftRight
          leftRight.ne
    · subst shoulder
      obtain ⟨target, adjacent, endpointNe, rightNe, leftNe⟩ :=
        shoulderCompletion right left rightShoulder leftShoulder leftRight.symm
          leftRight.ne.symm
      exact ⟨target, adjacent, endpointNe, leftNe, rightNe⟩
  · intro both
    exact nf.inducedMatching both.1 centreEndpoint both.2 leftRight.ne
      leftShoulder.1.symm rightShoulder.1
  · intro shoulder shoulderCases centreShoulder
    have degreeShoulder := nf.neighbourTight centreShoulder
    have degreeShoulderThree :
        object.degree shoulder = 3 := by
      rw [degreeShoulder, thresholdEq]
    refine ⟨degreeShoulder, ?_⟩
    intro target
    constructor
    · rintro ⟨targetAdj, targetEndpoint, targetLeft, targetRight⟩
      rcases shoulderCases with shoulderEq | shoulderEq
      · subst shoulder
        rcases exhaustThree left centre endpoint right target
            degreeShoulderThree centreShoulder.symm leftShoulder.1.symm leftRight
            centreEndpoint.ne rightShoulder.2.symm rightShoulder.1.ne targetAdj with
          rfl | rfl | rfl
        · rfl
        · exact (targetEndpoint rfl).elim
        · exact (targetRight rfl).elim
      · subst shoulder
        rcases exhaustThree right centre endpoint left target
            degreeShoulderThree centreShoulder.symm rightShoulder.1.symm leftRight.symm
            centreEndpoint.ne leftShoulder.2.symm leftShoulder.1.ne targetAdj with
          rfl | rfl | rfl
        · rfl
        · exact (targetEndpoint rfl).elim
        · exact (targetLeft rfl).elim
    · intro targetCentre
      subst target
      refine ⟨centreShoulder.symm, centreEndpoint.ne, ?_, ?_⟩
      · exact leftShoulder.2.symm
      · exact rightShoulder.2.symm
  · intro shoulder target shoulderCases targetAdj targetEndpoint targetLeft
      targetRight centreTarget
    by_cases targetCentre : target = centre
    · exact targetCentre
    have endpointDegreeThree : object.degree endpoint = 3 := by
      rw [endpointDegree, thresholdEq]
    have endpointTarget : ¬ object.graph.Adj endpoint target := by
      intro adjacent
      rcases exhaustThree endpoint centre left right target endpointDegreeThree
          centreEndpoint.symm leftShoulder.1 rightShoulder.1
          leftShoulder.2.symm rightShoulder.2.symm leftRight.ne adjacent with
        targetCentre' | targetLeft' | targetRight'
      · exact targetCentre targetCentre'
      · exact targetLeft targetLeft'
      · exact targetRight targetRight'
    rcases shoulderCases with shoulderEq | shoulderEq
    · subst shoulder
      exact False.elim (nf.noCommonNeighbourOutside centreEndpoint centreTarget
        targetEndpoint.symm endpointTarget leftShoulder.2
        leftShoulder.1 targetAdj.symm)
    · subst shoulder
      exact False.elim (nf.noCommonNeighbourOutside centreEndpoint centreTarget
        targetEndpoint.symm endpointTarget rightShoulder.2
        rightShoulder.1 targetAdj.symm)


/-- `lem:triangular-port-return`: the bridgeless return of every triangular port
enters through a shoulder and has rejected restored length. -/
theorem triangularPortReturn
    (bridgeless : BridgelessStatement object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (normal : HighCentreNormalFormStatement data object)
    (completion : TriangularShoulderCompletionStatement data object)
    (thresholdEq : data.threshold = 3)
    (powerOfTwo : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    TriangularPortReturnStatement data object := by
  classical
  intro centre centreHeavy endpoint endpointMem
  obtain ⟨left, right, leftShoulder, rightShoulder, leftNeRight,
    leftRight, completes, notBothCentral, centralCompletion⟩ :=
      completion centre centreHeavy endpoint endpointMem
  have centreEndpoint :=
    (Graph.mem_triangularEndpoints_iff.mp endpointMem).1
  have centreHigh : Graph.IsHighCentre object
      data.threshold centre :=
    Nat.lt_trans (Nat.lt_succ_self data.threshold) centreHeavy
  have nf := normal centre centreHigh
  have endpointDegreeThree :
      object.degree endpoint = 3 := by
    rw [nf.neighbourTight centreEndpoint, thresholdEq]
  have neighbourCard (vertex : object.Vertex) :
      (object.orderedNeighbors vertex).toFinset.card =
        object.degree vertex := by
    rw [List.toFinset_card_of_nodup
      (object.orderedNeighbors_nodup vertex),
      object.orderedNeighbors_length vertex]
  have exhaustEndpoint (target : object.Vertex)
      (targetAdj : object.graph.Adj endpoint target) :
      target = centre ∨ target = left ∨ target = right := by
    by_contra distinct
    push_neg at distinct
    rcases distinct with ⟨targetCentre, targetLeft, targetRight⟩
    have subset : ({centre, left, right, target} :
        Finset object.Vertex) ⊆
        (object.orderedNeighbors endpoint).toFinset := by
      intro item itemMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at itemMem
      rcases itemMem with rfl | rfl | rfl | rfl
      · simpa [object.mem_orderedNeighbors_iff] using
          centreEndpoint.symm
      · simpa [object.mem_orderedNeighbors_iff] using
          leftShoulder.1
      · simpa [object.mem_orderedNeighbors_iff] using
          rightShoulder.1
      · simpa [object.mem_orderedNeighbors_iff] using targetAdj
    have four : 4 ≤ ({centre, left, right, target} :
        Finset object.Vertex).card := by
      simp [leftShoulder.2, rightShoulder.2, leftNeRight,
        targetCentre, targetLeft, targetRight,
        leftShoulder.2.symm, rightShoulder.2.symm, leftNeRight.symm,
        targetCentre.symm, targetLeft.symm, targetRight.symm]
    have bound := Finset.card_le_card subset
    rw [neighbourCard, endpointDegreeThree] at bound
    omega
  let contraction : Graph.EdgeContraction object :=
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
      object centre endpoint left right :=
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
    let certificate : Graph.EdgeRootedReturn object
        Graph.EdgeRootedReturn.AnyLength :=
      { dart := ⟨(centre, endpoint), centreEndpoint⟩
        path := path
        isPath := forwardPath.reverse
        length_ok := trivial }
    apply avoids
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
    have firstQAdj : object.graph.Adj shoulder q.snd :=
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
            apply avoids
            let certificate : Graph.EdgeRootedReturn
                object Graph.EdgeRootedReturn.AnyLength :=
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
          rw [powerOfTwo]
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
            rw [pathLength, powerOfTwo]
            exact ⟨⟨2, by norm_num⟩, by norm_num, by norm_num⟩
          exact (show ¬ data.LengthOK (path.length + 1) from by
            intro accepted
            apply avoids
            let certificate : Graph.EdgeRootedReturn
                object Graph.EdgeRootedReturn.AnyLength :=
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
             simpa [shoulderEq] using firstQEdge⟩


/-- `lem:triangular-first-landing`: a shoulder completion edge lands centrally,
cross-triangularly, or outside, and exactly one of these. -/
theorem triangularFirstLanding
    (shoulderCompletion : TriangularShoulderCompletionStatement data object) :
    TriangularFirstLandingStatement data object := by
  classical
  intro centre centreHeavy ports portsNonempty portsSubset shoulders core
    completion central crossTriangular outside shoulderSpec coreSpec
    completionSpec centralSpec crossSpec outsideSpec endpoint shoulder target
    incidence
  obtain ⟨endpointMem, shoulderMem, shoulderTarget, targetEndpoint,
    targetNotOwnShoulders⟩ :=
      (completionSpec endpoint shoulder target).mp incidence
  have endpointTriangular := portsSubset endpointMem
  obtain ⟨left, right, leftShoulder, rightShoulder, leftNeRight,
    leftRight, _completes, _notBothCentral, centralOnly⟩ :=
      shoulderCompletion centre centreHeavy endpoint endpointTriangular
  have shoulderData := shoulderSpec endpoint endpointMem
  have pairSubset : ({left, right} :
      Finset object.Vertex) ⊆ shoulders endpoint := by
    intro vertex vertexMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at vertexMem
    rcases vertexMem with vertexEq | vertexEq
    · subst vertex
      exact (shoulderData.1 left).2 leftShoulder
    · subst vertex
      exact (shoulderData.1 right).2 rightShoulder
  have pairCard : ({left, right} :
      Finset object.Vertex).card = 2 := by
    simp [leftNeRight]
  have pairEq : ({left, right} :
      Finset object.Vertex) = shoulders endpoint :=
    Finset.eq_of_subset_of_card_le pairSubset (by
      rw [shoulderData.2.1, pairCard])
  have shoulderCases : shoulder = left ∨ shoulder = right := by
    have : shoulder ∈ ({left, right} :
        Finset object.Vertex) := by
      rw [pairEq]
      exact shoulderMem
    simpa using this
  have targetNotLeft : target ≠ left := by
    intro equality
    apply targetNotOwnShoulders
    rw [equality]
    exact (shoulderData.1 left).2 leftShoulder
  have targetNotRight : target ≠ right := by
    intro equality
    apply targetNotOwnShoulders
    rw [equality]
    exact (shoulderData.1 right).2 rightShoulder
  have noOtherNeighbour :
      object.graph.Adj centre target → target = centre := by
    intro centreTarget
    exact centralOnly.2 shoulder target shoulderCases shoulderTarget
      targetEndpoint targetNotLeft targetNotRight centreTarget
  have targetNotPorts : target ∉ ports := by
    intro targetPort
    have centreTarget :=
      (Graph.mem_triangularEndpoints_iff.mp (portsSubset targetPort)).1
    have targetCentre := noOtherNeighbour centreTarget
    subst target
    exact centreTarget.ne rfl
  have centreInCore : centre ∈ core :=
    (coreSpec centre).2 (Or.inl rfl)
  have crossNotOutside (crossing :
      crossTriangular endpoint shoulder target) :
      ¬ outside endpoint shoulder target := by
    intro external
    obtain ⟨_, other, otherMem, otherNe, targetShoulder⟩ :=
      (crossSpec endpoint shoulder target).mp crossing
    have targetCore : target ∈ core :=
      (coreSpec target).2
        (Or.inr (Or.inr ⟨other, otherMem, targetShoulder⟩))
    exact (outsideSpec endpoint shoulder target).mp external |>.2.1 targetCore
  have outsideNotCross (external : outside endpoint shoulder target) :
      ¬ crossTriangular endpoint shoulder target := by
    intro crossing
    exact crossNotOutside crossing external
  have centralNotCross (centralLanding :
      central endpoint shoulder target) :
      ¬ crossTriangular endpoint shoulder target := by
    intro crossing
    have targetCentre :=
      (centralSpec endpoint shoulder target).mp centralLanding |>.2
    obtain ⟨_, other, otherMem, _otherNe, targetShoulder⟩ :=
      (crossSpec endpoint shoulder target).mp crossing
    have targetNotCentre :=
      ((shoulderSpec other otherMem).1 target).1 targetShoulder |>.2
    exact targetNotCentre targetCentre
  have centralNotOutside (centralLanding :
      central endpoint shoulder target) :
      ¬ outside endpoint shoulder target := by
    intro external
    have targetCentre :=
      (centralSpec endpoint shoulder target).mp centralLanding |>.2
    exact (outsideSpec endpoint shoulder target).mp external |>.2.1
      (targetCentre ▸ centreInCore)
  have crossNotCentral (crossing :
      crossTriangular endpoint shoulder target) :
      ¬ central endpoint shoulder target := by
    intro centralLanding
    exact centralNotCross centralLanding crossing
  have outsideNotCentral (external : outside endpoint shoulder target) :
      ¬ central endpoint shoulder target := by
    intro centralLanding
    exact centralNotOutside centralLanding external
  refine ⟨?_, noOtherNeighbour, targetNotPorts⟩
  by_cases targetCentre : target = centre
  · have centralLanding : central endpoint shoulder target :=
      (centralSpec endpoint shoulder target).2 ⟨incidence, targetCentre⟩
    exact Or.inl ⟨centralLanding, centralNotCross centralLanding,
      centralNotOutside centralLanding⟩
  · by_cases targetCore : target ∈ core
    · rcases (coreSpec target).1 targetCore with
        targetCentre' | targetPort | ⟨other, otherMem, targetShoulder⟩
      · exact (targetCentre targetCentre').elim
      · exact (targetNotPorts targetPort).elim
      · have otherNe : other ≠ endpoint := by
          intro equality
          subst other
          exact targetNotOwnShoulders targetShoulder
        have crossing : crossTriangular endpoint shoulder target :=
          (crossSpec endpoint shoulder target).2
            ⟨incidence, other, otherMem, otherNe, targetShoulder⟩
        exact Or.inr (Or.inl ⟨crossing, crossNotCentral crossing,
          crossNotOutside crossing⟩)
    · have targetNotAdjacent :
          ¬ object.graph.Adj centre target := by
        intro adjacent
        exact targetCentre (noOtherNeighbour adjacent)
      have external : outside endpoint shoulder target :=
        (outsideSpec endpoint shoulder target).2
          ⟨incidence, targetCore, targetNotAdjacent⟩
      exact Or.inr (Or.inr ⟨external, outsideNotCentral external,
        outsideNotCross external⟩)


/-- `lem:triangular-cross-shoulder` on a target-avoiding object: at the cubic
baseline `δ = 3` a shoulder with four distinct neighbours is above the
baseline. -/
theorem triangularCrossShoulder
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (quadrilateral : data.LengthOK 4)
    (thresholdEq : data.threshold = 3) :
    TriangularCrossShoulderStatement data object := by
  classical
  intro centre centreHeavy ports portsNonempty portsSubset shoulders
    crossTriangular shoulderSpec crossSpec first firstMem second secondMem
    firstNeSecond
  dsimp only
  have chordOfDistinct : ∀ endpoint ∈ ports,
      ∀ left ∈ shoulders endpoint, ∀ right ∈ shoulders endpoint,
        left ≠ right → object.graph.Adj left right := by
    intro endpoint endpointMem left leftMem right rightMem leftNeRight
    obtain ⟨left₀, right₀, left₀Mem, right₀Mem, left₀NeRight₀, chord⟩ :=
      (shoulderSpec endpoint endpointMem).2.2
    have pairEq : ({left₀, right₀} :
        Finset object.Vertex) = shoulders endpoint :=
      Finset.eq_of_subset_of_card_le (by
        intro candidate candidateMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at candidateMem
        rcases candidateMem with h | h
        · simpa [h] using left₀Mem
        · simpa [h] using right₀Mem) (by
          simp [left₀NeRight₀, (shoulderSpec endpoint endpointMem).2.1])
    have every : ∀ vertex ∈ shoulders endpoint,
        vertex = left₀ ∨ vertex = right₀ := by
      intro vertex vertexMem
      have : vertex ∈ ({left₀, right₀} :
          Finset object.Vertex) := by
        rw [pairEq]
        exact vertexMem
      simpa using this
    rcases every left leftMem with rfl | rfl <;>
      rcases every right rightMem with rfl | rfl
    · exact (leftNeRight rfl).elim
    · exact chord
    · exact chord.symm
    · exact (leftNeRight rfl).elim
  have fourNeighbours : ∀ vertex a b c d,
      object.graph.Adj vertex a →
      object.graph.Adj vertex b →
      object.graph.Adj vertex c →
      object.graph.Adj vertex d →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        4 ≤ object.degree vertex := by
    intro vertex a b c d va vb vc vd ab ac ad bc bd cd
    have subset : ({a, b, c, d} :
        Finset object.Vertex) ⊆
          (object.orderedNeighbors vertex).toFinset := by
      intro candidate candidateMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at candidateMem
      rcases candidateMem with rfl | rfl | rfl | rfl
      · simpa [object.mem_orderedNeighbors_iff] using va
      · simpa [object.mem_orderedNeighbors_iff] using vb
      · simpa [object.mem_orderedNeighbors_iff] using vc
      · simpa [object.mem_orderedNeighbors_iff] using vd
    have cardFour : ({a, b, c, d} :
        Finset object.Vertex).card = 4 := by
      simp [ab, ac, ad, bc, bd, cd]
    have count := Finset.card_le_card subset
    rw [List.toFinset_card_of_nodup
      (object.orderedNeighbors_nodup vertex),
      object.orderedNeighbors_length] at count
    simpa [cardFour] using count
  have highOfDistinct : ∀ source target source' target',
      (crossTriangular first source target ∧
        crossTriangular second target source) →
      (crossTriangular first source' target' ∧
        crossTriangular second target' source') →
      (source ≠ source' ∨ target ≠ target') →
        ∃ shoulder,
          (shoulder ∈ shoulders first ∨ shoulder ∈ shoulders second) ∧
            data.threshold < object.degree shoulder := by
    intro source target source' target' edge edge' distinct
    have firstEdge := (crossSpec first source target).mp edge.1
    have secondEdge := (crossSpec second target source).mp edge.2
    have firstEdge' := (crossSpec first source' target').mp edge'.1
    have secondEdge' := (crossSpec second target' source').mp edge'.2
    by_cases sameSource : source = source'
    · have targetNe : target ≠ target' := by
        rcases distinct with sourceNe | targetNe
        · exact (sourceNe sameSource).elim
        · exact targetNe
      subst source'
      obtain ⟨other, otherMem, otherNe, sourceOther⟩ :
          ∃ other ∈ shoulders first, other ≠ source ∧
            object.graph.Adj source other := by
        obtain ⟨left, right, leftMem, rightMem, leftNeRight, chord⟩ :=
          (shoulderSpec first firstMem).2.2
        have sourceCases : source = left ∨ source = right := by
          have pairEq : ({left, right} :
              Finset object.Vertex) = shoulders first :=
            Finset.eq_of_subset_of_card_le (by
              intro vertex vertexMem
              simp only [Finset.mem_insert, Finset.mem_singleton] at vertexMem
              rcases vertexMem with h | h
              · simpa [h] using leftMem
              · simpa [h] using rightMem) (by
                simp [leftNeRight, (shoulderSpec first firstMem).2.1])
          have : source ∈ ({left, right} :
              Finset object.Vertex) := by
            rw [pairEq]
            exact firstEdge.2.1
          simpa using this
        rcases sourceCases with rfl | rfl
        · exact ⟨right, rightMem, leftNeRight.symm, chord⟩
        · exact ⟨left, leftMem, leftNeRight, chord.symm⟩
      refine ⟨source, Or.inl firstEdge.2.1, ?_⟩
      rw [thresholdEq]
      exact fourNeighbours source first other target target'
        (((shoulderSpec first firstMem).1 source).mp firstEdge.2.1).1.symm
        sourceOther firstEdge.2.2.1 firstEdge'.2.2.1
        ((((shoulderSpec first firstMem).1 other).mp otherMem).1.ne)
        firstEdge.2.2.2.1.symm firstEdge'.2.2.2.1.symm
        (by exact fun h => firstEdge.2.2.2.2.1 (h ▸ otherMem))
        (by exact fun h => firstEdge'.2.2.2.2.1 (h ▸ otherMem)) targetNe
    · by_cases sameTarget : target = target'
      · subst target'
        have sourceNe : source ≠ source' := sameSource
        obtain ⟨other, otherMem, otherNe, targetOther⟩ :
            ∃ other ∈ shoulders second, other ≠ target ∧
              object.graph.Adj target other := by
          obtain ⟨left, right, leftMem, rightMem, leftNeRight, chord⟩ :=
            (shoulderSpec second secondMem).2.2
          have targetCases : target = left ∨ target = right := by
            have pairEq : ({left, right} :
                Finset object.Vertex) = shoulders second :=
              Finset.eq_of_subset_of_card_le (by
                intro vertex vertexMem
                simp only [Finset.mem_insert, Finset.mem_singleton] at vertexMem
                rcases vertexMem with h | h
                · simpa [h] using leftMem
                · simpa [h] using rightMem) (by
                  simp [leftNeRight, (shoulderSpec second secondMem).2.1])
            have : target ∈ ({left, right} :
                Finset object.Vertex) := by
              rw [pairEq]
              exact secondEdge.2.1
            simpa using this
          rcases targetCases with rfl | rfl
          · exact ⟨right, rightMem, leftNeRight.symm, chord⟩
          · exact ⟨left, leftMem, leftNeRight, chord.symm⟩
        refine ⟨target, Or.inr secondEdge.2.1, ?_⟩
        rw [thresholdEq]
        exact fourNeighbours target second other source source'
          (((shoulderSpec second secondMem).1 target).mp secondEdge.2.1).1.symm
          targetOther secondEdge.2.2.1 secondEdge'.2.2.1
          ((((shoulderSpec second secondMem).1 other).mp otherMem).1.ne)
          secondEdge.2.2.2.1.symm secondEdge'.2.2.2.1.symm
          (by exact fun h => secondEdge.2.2.2.2.1 (h ▸ otherMem))
          (by exact fun h => secondEdge'.2.2.2.2.1 (h ▸ otherMem)) sourceNe
      · have sourceChord := chordOfDistinct first firstMem source
          firstEdge.2.1 source' firstEdge'.2.1 sameSource
        have targetChord := chordOfDistinct second secondMem target
          secondEdge.2.1 target' secondEdge'.2.1 sameTarget
        have sourceNeTarget' : source ≠ target' := by
          intro equality
          exact secondEdge.2.2.2.2.1 (equality ▸ secondEdge'.2.1)
        have targetNeSource' : target ≠ source' := by
          intro equality
          exact firstEdge.2.2.2.2.1 (equality ▸ firstEdge'.2.1)
        exact (Graph.not_quadrilateral avoids quadrilateral
          firstEdge.2.2.1 targetChord secondEdge'.2.2.1 sourceChord.symm
          sourceNeTarget' targetNeSource').elim
  refine ⟨highOfDistinct, ?_⟩
  intro low source target source' target' edge edge'
  by_cases sameSource : source = source'
  · refine ⟨sameSource, ?_⟩
    by_contra targetNe
    obtain ⟨shoulder, shoulderMem, high⟩ :=
      highOfDistinct source target source' target' edge edge'
        (Or.inr targetNe)
    exact (Nat.not_le_of_lt high) (low shoulder shoulderMem)
  · obtain ⟨shoulder, shoulderMem, high⟩ :=
      highOfDistinct source target source' target' edge edge'
        (Or.inl sameSource)
    exact ((Nat.not_le_of_lt high) (low shoulder shoulderMem)).elim


end Hypostructure.Graph.Contracts.TypeB
