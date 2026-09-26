import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[177]`, `lem:absorbed-germ-fan-data` (ii): decorated handoff fan data

For every occurrence in `[175]`'s case-(ii) complement, let `z` be the first
high vertex on its retained first-failure corridor.  The row uses the literal
prefix `J = corridor.prefixSupport traceEnd` as the counted core.  It proves
that `J` is connected and lies in the canonical remainder, takes `H = {z}` and
`K_z = N_G(z)`, and supplies an arm from every assigned neighbour to `J`.
The selection excludes every accepted fan return and label collision, while
`remainderNormalized` and `uncompressible` establish the remaining
`DecoratedHandoff.Admissible` clauses.  The high-degree bound gives two
distinct assigned neighbours.  Thus the value published at
`K .typeBFanEntry` is the manuscript's actual assigned-support/decorated-
envelope destination for the direct `[177] → [65]` edge.  No negative-charge
or zero-surplus premise is asserted at this handoff. -/
set_option maxHeartbeats 8000000 in
@[reducible] noncomputable def absorbedGermFanEnvelopeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.absorbedGermFanEnvelope
    { Requires := [K .selection, K .uncompressible, K .remainderNormalized,
        K .absorbedGermFanData]
      Produces := [K .typeBFanEntry]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selected := (inputs.get (K .selection)).down
      let uncompressible := (inputs.get (K .uncompressible)).down
      let normalized := (inputs.get (K .remainderNormalized)).down
      let fanData := (inputs.get (K .absorbedGermFanData)).down
      .cons (key := K .typeBFanEntry)
        ⟨by
          classical
          -- Generalize the current object after reading the ledger facts.
          have selectedRead := selected
          have uncompressibleRead := uncompressible
          have normalizedRead := normalized
          have fanDataRead := fanData
          revert selectedRead uncompressibleRead normalizedRead fanDataRead
          generalize inputs.current.object = object
          intro selected uncompressible normalized fanData
          letI : FinEnum object.Vertex :=
            object.vertices
          letI : Fintype object.Vertex := inferInstance
          letI : DecidableRel object.graph.Adj :=
            object.decideAdj
          change TypeBFanEntryStatement data.toParameters object
          apply Or.inr
          apply Or.inl
          simp only [AbsorbedGermDecoratedAssignedSupportStatement]
          change AbsorbedGermFanDataStatement data.toParameters object at fanData
          simp only [AbsorbedGermFanDataStatement] at fanData
          obtain ⟨routing, _incidence, _candidates, _disjointFamily,
              _corridorLoss, _familyWitness, fanData⟩ := fanData
          refine ⟨routing, ?_⟩
          intro epsilon notCandidate
          obtain ⟨firstIndex, firstBound, high, earlierBound,
              neighboursCubic⟩ := fanData epsilon notCandidate
          let classified := coldRoutedClassified data.toParameters object routing
          let state := classified.state
          let stateOne := Classical.choose_spec state
          let componentAt := Classical.choose stateOne
          let stateTwo := Classical.choose_spec stateOne
          let corridorAt := Classical.choose stateTwo
          let stateThree := Classical.choose_spec stateTwo
          let presentationAt := Classical.choose stateThree
          let stateFour := Classical.choose_spec stateThree
          let indexAt := Classical.choose stateFour
          let stateBundle := Classical.choose_spec stateFour
          let routed : ColdEligibleHalfEdge data.toParameters object := epsilon
          let component := componentAt routed
          let corridor := corridorAt routed
          let _presentation := presentationAt routed
          let _index := indexAt routed
          let centre := corridor.head firstIndex
          change data.threshold < object.degree centre at high
          change (∀ neighbour : object.Vertex,
            object.graph.Adj centre neighbour →
              object.degree neighbour = data.threshold) at neighboursCubic
          refine ⟨centre, ⟨routing, epsilon, rfl, firstIndex, rfl,
            firstBound, high, earlierBound, neighboursCubic, ?_⟩⟩
          let traceEnd := coldRoutedTraceEnd data.toParameters object routing epsilon
          change firstIndex.1 ≤ traceEnd at firstBound
          let core := corridor.prefixSupport traceEnd
          have centreCore : centre ∈ core := by
            apply (corridor.mem_prefixSupport traceEnd centre).2
            refine ⟨corridor.inside.1.getVert firstIndex.1, ?_, rfl⟩
            have member := SimpleGraph.Walk.getVert_mem_support
              (corridor.inside.1.take traceEnd) firstIndex.1
            simpa only [SimpleGraph.Walk.take_getVert,
              Nat.min_eq_right firstBound] using member
          have coreInside : core ⊆ object.remainderSupport
              (canonicalWindowPacking data.toParameters object) := by
            exact (corridor.prefixSupport_subset_component traceEnd).trans
              (stateBundle.2.2.2.1 routed)
          have avoids : ¬ Graph.HasCycleWithLength data.LengthOK
              object := selected.1
          have denied : ∀ c a b,
              ¬ handoffAbsorbing data.toParameters object
                (canonicalWindowPacking data.toParameters object) c a b :=
            fun _ _ _ collision => avoids
              (Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision
                data.degenerateClosureRejected collision)
          let assigned := object.graph.neighborFinset centre
          let arm := fun next : object.Vertex =>
            if next ∈ core then [next] else [next, centre]
          let envelope : Graph.DecoratedHandoff.Envelope object
              data.LengthOK (handoffHighDegree data.toParameters object)
              (handoffAbsorbing data.toParameters object
                (canonicalWindowPacking data.toParameters object)) :=
            { core := core
              decorations := {centre}
              decorations_high := by
                intro current member
                simp only [Finset.mem_singleton] at member
                simpa [member] using high
              assigned := fun _ => assigned
              assigned_nonempty := by
                intro current member
                simp only [Finset.mem_singleton] at member
                subst current
                apply Finset.card_pos.mp
                rw [show assigned.card = object.degree centre by
                  simp [assigned, Graph.FiniteObject.degree,
                    SimpleGraph.card_neighborFinset_eq_degree]]
                exact Nat.zero_lt_of_lt high
              assigned_adj := by
                intro current member next nextMember
                simp only [Finset.mem_singleton] at member
                subst current
                exact (SimpleGraph.mem_neighborFinset _ _ _).1 nextMember
              arm := fun _ next => arm next
              arm_issued := by
                intro current member next nextMember
                simp only [Finset.mem_singleton] at member
                subst current
                by_cases nextCore : next ∈ core <;> simp [arm, nextCore]
              arm_chain := by
                intro current member next nextMember
                simp only [Finset.mem_singleton] at member
                subst current
                have adjacent :=
                  (SimpleGraph.mem_neighborFinset _ _ _).1 nextMember
                by_cases nextCore : next ∈ core
                · simp [arm, nextCore]
                · simpa [arm, nextCore] using adjacent.symm
              arm_nodup := by
                intro current member next nextMember
                simp only [Finset.mem_singleton] at member
                subst current
                have adjacent :=
                  (SimpleGraph.mem_neighborFinset _ _ _).1 nextMember
                by_cases nextCore : next ∈ core
                · simp [arm, nextCore]
                · simp [arm, nextCore, adjacent.ne.symm]
              arm_lands := by
                intro current member next nextMember
                simp only [Finset.mem_singleton] at member
                subst current
                by_cases nextCore : next ∈ core
                · exact ⟨next, by simp [arm, nextCore], nextCore⟩
                · exact ⟨centre, by simp [arm, nextCore], centreCore⟩
              arm_interior := by
                intro current member next nextMember vertex vertexMember alternative
                simp only [Finset.mem_singleton] at member
                subst current
                have adjacent :=
                  (SimpleGraph.mem_neighborFinset _ _ _).1 nextMember
                by_cases nextCore : next ∈ core
                · simp only [arm, if_pos nextCore, List.mem_singleton] at vertexMember
                  simp [vertexMember, arm, nextCore]
                · simp only [arm, if_neg nextCore, List.mem_cons,
                    List.not_mem_nil, or_false] at vertexMember
                  rcases vertexMember with rfl | rfl
                  · exfalso
                    simp only [Finset.mem_singleton] at alternative
                    rcases alternative with inCore | equal | equal
                    · exact nextCore inCore
                    · exact adjacent.ne equal.symm
                    · exact adjacent.ne equal.symm
                  · simp [arm, nextCore]
              fanSafe := by
                intro current member first firstMember second secondMember different
                simp only [Finset.mem_singleton] at member
                subst current
                have firstAdj :=
                  (SimpleGraph.mem_neighborFinset _ _ _).1 firstMember
                have secondAdj :=
                  (SimpleGraph.mem_neighborFinset _ _ _).1 secondMember
                exact ⟨Graph.DecoratedHandoff.fanSafe_geometric firstAdj secondAdj
                    different avoids,
                  denied centre first second⟩ }
          have packingSpec := Classical.choose_spec
            (object.exists_windowPacking_card_eq data.windowOrder)
          have packingMaximal : ∀ window : Finset object.Vertex,
              object.InducesWindow data.windowOrder window →
                ∃ member ∈ canonicalWindowPacking data.toParameters object,
                  ¬ Disjoint window member := by
            intro window induced
            exact object.exists_mem_not_disjoint_of_card_eq
              data.windowOrder_pos packingSpec.1 packingSpec.2 induced
          have coreSafe : handoffWindowFree data.toParameters object core := by
            constructor
            · intro window subset induced
              exact (normalized (canonicalWindowPacking data.toParameters object)
                packingSpec.1 packingMaximal window
                  (subset.trans coreInside)).1 induced
            · intro internal subset
              exact (normalized (canonicalWindowPacking data.toParameters object)
                packingSpec.1 packingMaximal internal
                  (subset.trans coreInside)).2
          have admissible : Graph.DecoratedHandoff.Admissible
              object data.LengthOK
              (handoffUncompressible data.toParameters object)
              (handoffWindowFree data.toParameters object) envelope :=
            Graph.DecoratedHandoff.admissible_of_envelope avoids coreSafe
              uncompressible
          have assignedTwo : 1 < assigned.card := by
            rw [show assigned.card = object.degree centre by
              simp [assigned, Graph.FiniteObject.degree,
                SimpleGraph.card_neighborFinset_eq_degree]]
            have thresholdLower := data.three_le_threshold
            omega
          obtain ⟨first, firstMember, second, secondMember, different⟩ :=
            Finset.one_lt_card.mp assignedTwo
          have firstAssigned : first ∈ envelope.assigned centre := by
            simpa [envelope] using firstMember
          have secondAssigned : second ∈ envelope.assigned centre := by
            simpa [envelope] using secondMember
          refine And.intro (corridor.prefixSupport_connectedOn traceEnd) ?_
          refine And.intro coreInside ?_
          refine Exists.intro envelope ?_
          refine And.intro rfl ?_
          refine And.intro rfl ?_
          refine And.intro admissible ?_
          refine Exists.intro first ?_
          refine Exists.intro second ?_
          exact And.intro different (And.intro firstAssigned secondAssigned)
        ⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
