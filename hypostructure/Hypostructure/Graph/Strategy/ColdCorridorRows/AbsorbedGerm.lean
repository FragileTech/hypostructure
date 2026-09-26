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

/-! ## Node `[175]`, `lem:absorbed-germ-fan-data`: the per-half-edge dichotomy

On the absorbed-configuration residual every selected branch-excess half-edge
`ε` of an ambient-cubic cold window has a return corridor (`lem:bridgeless`)
and a first-failure exchange germ; the lemma's dichotomy is *per half-edge*,
by whether the germ's support `J` meets a vertex above the threshold.  Case
(i): `J` is subcubic, so `ε`'s germ is a candidate of `lem:cold-germ-extraction`
and is charged in full.  Case (ii): `J` contains a vertex `z` above the
threshold; node `[10]` (`K .slackIndependent`) makes every neighbour of `z`
sit exactly at the threshold, so `z` is a heavy centre.  The row publishes
that dichotomy for every selected half-edge, on the literal residual; the
exhaustive object-level decision that follows (`absorbedGermDichotomy`) only
chooses which continuation closes the branch. -/
set_option maxHeartbeats 4000000 in
@[reducible] noncomputable def absorbedGermSplitRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.absorbedGermSplit
    { Requires := [K .coldGermCandidates, K .coldHandoffTransfer,
        K .slackIndependent]
      Produces := [K .absorbedGermSplit]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let family := (inputs.get (K .coldGermCandidates)).down
      let handoff := (inputs.get (K .coldHandoffTransfer)).down
      let independent := (inputs.get (K .slackIndependent)).down
      .cons (key := K .absorbedGermSplit)
        ⟨by
          classical
          -- Generalize the current object after reading the ledger, so the
          -- retained cold witnesses are destructured over an abstract object.
          have familyRead := family
          have handoffRead := handoff
          have independentRead := independent
          have baselineRead : Graph.MinimumDegreeAtLeast data.threshold
              inputs.current.object := inputs.current.baseline
          revert familyRead handoffRead independentRead baselineRead
          generalize inputs.current.object = object
          intro family handoff independent baseline
          letI : FinEnum object.Vertex := object.vertices
          letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
          letI : Fintype (ColdEligibleHalfEdge data.toParameters object) :=
            coldEligibleHalfEdgeFintype data.toParameters object
          change ColdGermCandidatesStatement data.toParameters object at family
          rcases family with
            ⟨routing, _incidence, _candidates, _disjointFamily, _corridorLoss,
              _familyWitness⟩
          change AbsorbedGermSplitStatement data.toParameters object
          simp only [AbsorbedGermSplitStatement]
          refine ⟨routing, ?_⟩
          intro epsilon
          let classified := coldRoutedClassified data.toParameters object routing
          let state := classified.state
          rcases handoff state epsilon with subcubic | high
          · apply Or.inl
            exact Finset.mem_filter.2
              ⟨Finset.mem_univ _,
                Classical.choose_spec routing.surviving.holds epsilon,
                subcubic⟩
          · rcases high with
              ⟨first, firstBound, firstHigh, earlierBound, _root⟩
            refine Or.inr ⟨first, firstBound, firstHigh, earlierBound,
              fun neighbour adjacent => ?_⟩
            apply le_antisymm
            · by_contra above
              push Not at above
              exact independent ((coldOccurrenceCorridorAt data.toParameters object classified
                epsilon).head first) neighbour firstHigh above adjacent
            · exact le_trans baseline (object.minDegree_le_degree neighbour)⟩
        .nil)

/-! ## Nodes `[174]`--`[177]`, `lem:absorbed-germ-fan-data`: the absorbed-germ split

On the absorbed-germ residual (`[173]`'s no arm), node `[175]` tests whether
the literal case-(i) occurrence class is nonempty.  The yes arm records only
that exact predicate as `K .coldPositiveGerm`; node `[176]` obtains the
candidate extraction from its existing node-`[153]` owner.  Independently of
that test, `absorbedGermSplitRow` retains the case-(ii) witness for every
occurrence outside the candidate set, so mixed families continue through both
paper routes without losing either subfamily.  On the no arm the same
complement is the whole selected family. -/
noncomputable def absorbedGermDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .absorbedGermSplit) known]
    [FactKeys.Has (K .coldGermCandidates) known]
    (positiveFresh : K .coldPositiveGerm ∉ known)
    (absorbedFresh : K .absorbedGermFanData ∉ known) :
    Decision (K .coldPositiveGerm) (K .absorbedGermFanData) previous := by
  classical
  let split := (previous.get (K .absorbedGermSplit)).down
  let object := current.object
  letI : FinEnum object.Vertex := object.vertices
  change AbsorbedGermSplitStatement data.toParameters object at split
  simp only [AbsorbedGermSplitStatement] at split
  let routing := Classical.choose split
  let alternatives := Classical.choose_spec split
  let routedCandidates := coldRoutedCandidates data.toParameters object routing
  exact Decision.run previous (K .coldPositiveGerm) (K .absorbedGermFanData)
    `Hypostructure.Graph.Strategy.Spine.absorbedGermDichotomy
    (if positive : 0 < routedCandidates.card then
      .inl ⟨by
        change ColdPositiveGermStatement data.toParameters object
        exact ⟨routing, positive⟩⟩
    else
      .inr ⟨by
        let family := (previous.get (K .coldGermCandidates)).down
        change ColdGermCandidatesStatement data.toParameters object at family
        rcases family with
          ⟨familyRouting, incidence, candidates, disjointFamily, corridorLoss,
            familyWitness⟩
        have routingEq : familyRouting = routing := Subsingleton.elim _ _
        subst familyRouting
        change AbsorbedGermFanDataStatement data.toParameters object
        simp only [AbsorbedGermFanDataStatement]
        refine ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
          familyWitness, ?_⟩
        intro epsilon _notCandidate
        rcases alternatives epsilon with candidate | high
        · exact (positive (Finset.card_pos.2 ⟨_, candidate⟩)).elim
        · exact high⟩)
    positiveFresh absorbedFresh

/-- Node `[177]` on `[175]`'s positive arm.  The node-`[153]` package already
contains the exact candidate/loss identity and the `B_cold·σ(G)` loss bound;
the per-incidence split supplies the least-high witness on its complement.
This owner combines those two previously proved facts in the ledger.  It is
run before the decorated-envelope owner, so a mixed family publishes its
complete case-(ii) accounting without re-proving node `[153]`. -/
@[reducible] noncomputable def absorbedGermFanDataRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.absorbedGermFanData
    { Requires := [K .absorbedGermSplit, K .coldGermCandidates]
      Produces := [K .absorbedGermFanData]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let split := (inputs.get (K .absorbedGermSplit)).down
      let family := (inputs.get (K .coldGermCandidates)).down
      .cons (key := K .absorbedGermFanData)
        ⟨by
          classical
          let object := inputs.current.object
          letI : FinEnum object.Vertex := object.vertices
          change AbsorbedGermSplitStatement data.toParameters object at split
          change ColdGermCandidatesStatement data.toParameters object at family
          simp only [AbsorbedGermSplitStatement] at split
          obtain ⟨splitRouting, alternatives⟩ := split
          obtain ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
              familyWitness⟩ := family
          have routingEq : splitRouting = routing := Subsingleton.elim _ _
          subst splitRouting
          change AbsorbedGermFanDataStatement data.toParameters object
          simp only [AbsorbedGermFanDataStatement]
          refine ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
            familyWitness, ?_⟩
          intro epsilon notCandidate
          rcases alternatives epsilon with candidate | high
          · exact (notCandidate candidate).elim
          · exact high⟩
        .nil)

/-- Node `[176]`: the positive class chosen at `[175]` is the exact candidate
set inside node `[153]`'s retained extraction.  Hence the already-published
greedy extraction theorem makes that same disjoint family nonempty. -/
@[reducible] noncomputable def absorbedGermFamilyPositiveRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.absorbedGermFamilyPositive
    { Requires := [K .coldPositiveGerm, K .coldGermCandidates]
      Produces := [K .coldGermFamilyPositive]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let positive := (inputs.get (K .coldPositiveGerm)).down
      let family := (inputs.get (K .coldGermCandidates)).down
      .cons (key := K .coldGermFamilyPositive)
        ⟨by
          classical
          let object := inputs.current.object
          letI : FinEnum object.Vertex := object.vertices
          change ColdPositiveGermStatement data.toParameters object at positive
          change ColdGermCandidatesStatement data.toParameters object at family
          rcases positive with ⟨positiveRouting, positiveCard⟩
          rcases family with
            ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
              familyWitness⟩
          have routingEq : positiveRouting = routing := Subsingleton.elim _ _
          subst positiveRouting
          simp only [ColdGermFamilyWitness] at familyWitness
          rcases familyWitness with
            ⟨incidenceEq, candidatesEq, candidateFamily, extracted,
              noncandidateClassified, occurrenceCount, selectedCount,
              lossBound, quantitative⟩
          have candidatePositive : 0 < candidates.card := by
            rw [candidatesEq]
            exact positiveCard
          have disjointPositive : 0 < disjointFamily.card :=
            Graph.ColdCorridor.coldGerm_nonempty extracted.2.2 candidatePositive
          change ColdGermFamilyPositiveStatement data.toParameters object
          refine ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
            ?_, disjointPositive⟩
          simp only [ColdGermFamilyWitness]
          exact ⟨incidenceEq, candidatesEq, candidateFamily, extracted,
            noncandidateClassified, occurrenceCount, selectedCount,
            lossBound, quantitative⟩⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
