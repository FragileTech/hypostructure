import Hypostructure.Graph.DeletionCriticality

/-!
# Graph deletion-criticality fixture

The complete graph on two vertices is a minimal graph of minimum degree one.
The fixture derives its no-subobject certificate, registers it after the
context in one accumulated ledger, and runs Core's sealed criticality stage
(manuscript nodes `[9]`--`[10]`) against the graph edge-deletion semantics
through typed queries.  Reading the two appended entries back gives the graph
certificate: its unique edge has a tight endpoint at the generic threshold `1`,
and its slack vertices are independent.
-/

namespace Hypostructure.Fixtures.GraphDeletionCriticality

open Hypostructure.Graph
open Hypostructure.Core.Residual

abbrev k2 : FiniteObject where
  Vertex := Fin 2
  graph := ⊤
  vertices := inferInstance
  decideAdj := inferInstance

def Baseline : FiniteObject → Prop :=
  MinimumDegreeAtLeast 1

def BranchState (_object : FiniteObject) := Unit

def Target (_object : FiniteObject) : Prop := False

@[simp]
theorem k2_vertexCount : k2.vertexCount = 2 := by
  decide

@[simp]
theorem k2_edgeCount : k2.edgeCount = 1 := by
  decide

theorem k2_baseline : Baseline k2 := by
  change 1 ≤ (⊤ : SimpleGraph (Fin 2)).minDegree
  rw [SimpleGraph.minDegree_top]
  decide

theorem k2_avoids : Not (Target k2) := by
  simp [Target]

def context : Core.MinimalCounterexampleContext
    (problem Baseline BranchState) Target
    (lexicographicProgress Baseline BranchState) where
  toAvoidingContext := {
    toBranchContext := {
      G := k2
      baseline := k2_baseline
      state := ()
    }
    avoids := k2_avoids
  }
  minimal := by
    intro candidate smaller baseline
    exfalso
    rw [lexicographicProgress_smaller_iff,
      FiniteObject.lexicographicallySmaller_iff] at smaller
    have candidateNonempty : Nonempty candidate.Vertex := by
      cases isEmpty_or_nonempty candidate.Vertex with
      | inl empty =>
          letI : IsEmpty candidate.Vertex := empty
          have zero : candidate.minDegree = 0 := by
            letI : FinEnum candidate.Vertex := candidate.vertices
            letI : DecidableRel candidate.graph.Adj := candidate.decideAdj
            unfold FiniteObject.minDegree
            exact SimpleGraph.minDegree_of_isEmpty candidate.graph
          exact False.elim (by
            change 1 ≤ candidate.minDegree at baseline
            omega)
      | inr nonempty => exact nonempty
    letI : FinEnum candidate.Vertex := candidate.vertices
    letI : DecidableRel candidate.graph.Adj := candidate.decideAdj
    letI : Nonempty candidate.Vertex := candidateNonempty
    have minDegreeLt : candidate.minDegree < candidate.vertexCount := by
      change candidate.graph.minDegree < candidate.vertices.card
      simpa [FinEnum.card_eq_fintypeCard] using
        candidate.graph.minDegree_lt_card
    have twoLeVertices : 2 ≤ candidate.vertexCount := by
      change 1 ≤ candidate.minDegree at baseline
      omega
    rcases smaller with vertexLt | ⟨_vertexEq, edgeLt⟩
    · rw [k2_vertexCount] at vertexLt
      omega
    · obtain ⟨vertex⟩ := candidateNonempty
      have degreePos : 0 < candidate.degree vertex := by
        have degreeLower := candidate.minDegree_le_degree vertex
        change 1 ≤ candidate.minDegree at baseline
        omega
      have graphDegreePos : 0 < candidate.graph.degree vertex := by
        exact degreePos
      obtain ⟨neighbor, adjacent⟩ :=
        (candidate.graph.degree_pos_iff_exists_adj vertex).mp graphDegreePos
      have edgeMember : s(vertex, neighbor) ∈ candidate.graph.edgeFinset :=
        SimpleGraph.mem_edgeFinset.mpr adjacent
      have edgeCountPos : 0 < candidate.edgeCount := by
        unfold FiniteObject.edgeCount
        exact Finset.card_pos.mpr ⟨_, edgeMember⟩
      rw [k2_edgeCount] at edgeLt
      omega

def minimalityProfile :
    ProperSubgraphMinimalityProfile Baseline BranchState Target where
  targetMonotone := {
    map := by
      intro _source _subgraph target
      exact target
  }
  stateOf := fun _object => ()

/-- Manuscript node `[8]` in Core's own coordinates: the no-subobject
certificate that Core's criticality node consumes. -/
def noSubobject :
    Core.Minimality.NoSubobjectBaselineCertificate
      (toCoreProfile minimalityProfile) context :=
  Core.Minimality.deriveNoSubobjectBaseline
    (toCoreProfile minimalityProfile) context

/-- The root residual owns the selected context. -/
structure Input where
  context : Core.MinimalCounterexampleContext
    (problem Baseline BranchState) Target
    (lexicographicProgress Baseline BranchState)

def input : Input := ⟨context⟩

abbrev Root := Ledger Input

def root : Root := Ledger.initial input

def rootInputQuery : Query Root (fun _root => Input) :=
  Query.residual

def rootContextQuery : Query Root (fun _root =>
    Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) :=
  rootInputQuery.map fun _root value => value.context

/-- The inherited no-subobject certificate is the next entry of the same
accumulated ledger, with its type indexed by the context already registered. -/
abbrev Previous := Ledger.Extension Root (fun root =>
  Core.Minimality.NoSubobjectBaselineCertificate
    (toCoreProfile minimalityProfile) (rootContextQuery root))

def previous : Previous :=
  Ledger.extend root noSubobject

def contextLedgerQuery : Query Previous (fun _previous =>
    Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) :=
  rootContextQuery.preserve

def noSubobjectQuery :
    DeletionCriticalityNoSubobjectQuery
      (minimumDegreeDeletionCriticalityProfile 1) minimalityProfile
      contextLedgerQuery :=
  Query.latest

/-- Core appends both entries of manuscript nodes `[9]`--`[10]` to the literal
incoming ledger; the graph layer supplied only the edge-deletion semantics. -/
def stage :
    MinimumDegreeDeletionCriticalityStage 1 minimalityProfile
      contextLedgerQuery noSubobjectQuery :=
  executeMinimumDegreeDeletionCriticality 1 minimalityProfile
    contextLedgerQuery noSubobjectQuery previous

def certificateQuery :=
  minimumDegreeDeletionCriticalityQuery 1 minimalityProfile contextLedgerQuery
    noSubobjectQuery

def dart : k2.graph.Dart :=
  ⟨((0 : Fin 2), (1 : Fin 2)), by decide⟩

theorem executor_preserves_previous : stage.previous.previous = previous :=
  rfl

theorem generated_tight_endpoint :
    k2.degree dart.fst = 1 ∨ k2.degree dart.snd = 1 := by
  exact (certificateQuery stage).tightEndpoint dart

theorem generated_slack_independence {left right : k2.Vertex}
    (leftSlack : 2 ≤ k2.degree left)
    (rightSlack : 2 ≤ k2.degree right) :
    Not (k2.graph.Adj left right) := by
  exact (certificateQuery stage).slackVerticesIndependent
    leftSlack rightSlack

#print axioms FiniteObject.deleteEdge_preserves_minDegree
#print axioms deletionCriticalityOfLedger
#print axioms executeDeletionCriticality
#print axioms executeMinimumDegreeDeletionCriticality
#print axioms generated_tight_endpoint
#print axioms generated_slack_independence

end Hypostructure.Fixtures.GraphDeletionCriticality
