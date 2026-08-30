import Hypostructure.Graph.TypeBOverlapResponseCoordinate
import Hypostructure.Graph.TypeABCertificate
import Hypostructure.Graph.HighCentreNormalForm
import Hypostructure.Graph.TypeBDirectCycle
import Hypostructure.Graph.DeclaredRankQuotient

/-!
# Type B overlap reflection

This module records all five clauses of `lem:typeB-global-local-reflection`.
Clause (d) is stated on the literal finite overlap-coordinate schedule and is
proved by the canonical declared-rank quotient routing theorem; no response
classification is stored in the obstruction.
-/

namespace Hypostructure.Graph

universe u

namespace TypeBRefinedSupport

open Classical

noncomputable section

/-- The selected incidences which are literally on the packed-window side of
the canonical B1 carrier. -/
def CandidateData.packedWindowIncidences {object : FiniteObject.{u}}
    (data : CandidateData object) (threshold : ℕ)
    (packing : Finset (Finset object.Vertex)) (hub : object.Vertex) :
    Finset (object.Vertex × object.Vertex) :=
  (data.selectedIncidences threshold packing hub).filter fun incidence =>
    incidence.2 ∈ object.windowSupport packing

/-- Every packed-window carrier selected by an eligible live candidate is a
literal remainder-to-window incidence counted by the ordinary stub supply. -/
theorem CandidateData.packedWindowIncidences_subset_localWindowBoundaryIncidences
    {object : FiniteObject.{u}} {threshold dischargeScale : ℕ}
    {packing : Finset (Finset object.Vertex)}
    {piece : CanonicalPiece object packing}
    {assigned : Finset object.Vertex}
    {hub : object.Vertex} {data : CandidateData object}
    (eligible : data ∈ candidateFamily object threshold dischargeScale
      packing piece.vertices assigned hub) :
    data.packedWindowIncidences threshold packing hub ⊆
      object.localWindowBoundaryIncidences packing piece.vertices := by
  intro incidence member
  have candidate := (mem_candidateFamily_iff.mp eligible).2
  have selected := (Finset.mem_filter.mp member).1
  have window := (Finset.mem_filter.mp member).2
  cases data with
  | certificate profile assigned =>
      simp [CandidateData.packedWindowIncidences,
        CandidateData.selectedIncidences] at member
  | positive profile localReserve chosenNonWindow =>
      have chargedSubset :
          CandidateData.chargedVertices
              (.positive profile localReserve chosenNonWindow)
              threshold hub ⊆ piece.vertices :=
        candidate.2.2.2.1
      have chosenSubset :
          chosenNonWindow ⊆
            TypeBHybridIncidence.nonWindowIncidenceSet object threshold
              profile.envelope (object.windowSupport packing) hub :=
        candidate.2.2.2.2.2.2.2.2.2
      have windowMember :
          incidence ∈ TypeBHybridIncidence.windowIncidenceSet object threshold
            profile.envelope (object.windowSupport packing) hub := by
        rcases Finset.mem_union.mp selected with inWindow | inLocalQ
        · exact inWindow
        · have nonWindow := chosenSubset inLocalQ
          exact absurd window
            ((Finset.mem_filter.mp nonWindow).2)
      have incidenceMember := (Finset.mem_filter.mp windowMember).1
      rcases (TypeBHybridIncidence.mem_incidences_iff
          object threshold profile.envelope (object.windowSupport packing)
            hub incidence).mp incidenceMember with ⟨ownerClosed, farMember⟩
      have ownerInPiece : incidence.1 ∈ piece.vertices := by
        apply chargedSubset
        simp only [CandidateData.chargedVertices, Finset.mem_union]
        exact Or.inl ownerClosed
      have adjacent : object.graph.Adj incidence.1 incidence.2 :=
        (TypeBHybridIncidence.mem_nonHubIncidences_iff.mp farMember).2
      exact (object.mem_localWindowBoundaryIncidences_iff
        packing piece.vertices incidence).mpr
          ⟨ownerInPiece, adjacent,
            piece.vertices_subset_remainder ownerInPiece, window⟩

/-- All five clauses of the manuscript's Type B global-to-local reflection. -/
structure GlobalLocalReflectionACE
    (presentation : TypeAB.Presentation.{u})
    (object : FiniteObject.{u}) (order : ℕ) (LengthOK : ℕ → Prop)
    (threshold dischargeScale : ℕ)
    {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing)
    (assigned : Finset object.Vertex)
    (obstruction : OverlapObstruction object threshold dischargeScale
      packing piece.vertices assigned) : Prop where
  /-- Manuscript clause (a). -/
  contextualDyadicSafety : TypeAB.ContextuallyDyadicSafe presentation object
  /-- Manuscript clause (b), first assertion. -/
  centresIndependent :
    ∀ left ∈ obstruction.demands, ∀ right ∈ obstruction.demands,
      left ≠ right → ¬ object.graph.Adj left right
  /-- Manuscript clause (b), second assertion. -/
  neighbourTight :
    ∀ hub ∈ obstruction.demands, ∀ ⦃vertex : object.Vertex⦄,
      object.graph.Adj hub vertex → object.degree vertex = threshold
  /-- Manuscript clause (c), incidence-supply assertion. -/
  packedWindowCompatible :
    ∀ hub ∈ obstruction.demands, ∀ data,
      data ∈ candidateFamily object threshold dischargeScale
          packing piece.vertices assigned hub →
        data.packedWindowIncidences threshold packing hub ⊆
          object.localWindowBoundaryIncidences packing piece.vertices
  /-- Manuscript clause (c), direct same-window and two-window exclusion. -/
  directCycleFree :
    ∀ hub ∈ obstruction.demands,
      TypeBDirectCycle.DirectCycleFree object order LengthOK packing hub
  /-- Manuscript clause (d).  Every rank-reducing identification attempted on
  the literal overlap-coordinate schedule is routed by the declared response
  calculus: degree-profile failure, contextual target defect, a proper
  replacement, or a smaller closed representative. -/
  replacementObstruction :
    ∀ attempt : AttemptedQuotient (TypeAB.Baseline presentation)
        presentation.Target object
        (overlapCoordinateSchedule object threshold dischargeScale packing
          piece.vertices assigned obstruction).toFinset
        (fun _ => obstruction.overlapSupport),
      attempt.support = obstruction.overlapSupport →
      ¬ Set.InjOn attempt.label
        ↑(overlapCoordinateSchedule object threshold dischargeScale packing
          piece.vertices assigned obstruction).toFinset →
      (∃ left right, attempt.Identifies left right ∧
          left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile) ∨
        (∃ left right, attempt.Identifies left right ∧
          Response.TargetDefect presentation.Target left right) ∨
        Strategy.InterfaceReplacement.ReplacementSupport
          (TypeAB.Baseline presentation) presentation.Target object
          attempt.support ∨
        (∃ representative : FiniteObject.{u},
          representative.LexicographicallySmaller object ∧
            TypeAB.Baseline presentation representative ∧
              (presentation.Target representative → presentation.Target object))
  /-- Manuscript clause (e).  This is stated for every proper nonempty demand
  subfamily and therefore includes every proper connected sub-obstruction. -/
  minimalOverlap :
    ∀ sub : Finset object.Vertex, sub ⊂ obstruction.demands → sub.Nonempty →
      HasDisjointChoice object threshold dischargeScale
        packing piece.vertices assigned sub

/-- Clauses (a)--(c) and (e) are inherited or derived on the literal overlap
support.  Normal form supplies clause (b); candidate provenance and the
canonical remainder component supply the incidence part of (c); the exact
direct-cycle-free fact supplies its cycle exclusion; obstruction minimality is
clause (e). -/
theorem globalLocalReflectionACE
    {presentation : TypeAB.Presentation.{u}}
    {object : FiniteObject.{u}} {order : ℕ} {LengthOK : ℕ → Prop}
    {threshold dischargeScale : ℕ}
    {packing : Finset (Finset object.Vertex)}
    {piece : CanonicalPiece object packing}
    {assigned : Finset object.Vertex}
    (obstruction : OverlapObstruction object threshold dischargeScale
      packing piece.vertices assigned)
    (targetSafe : TypeAB.ContextuallyDyadicSafe presentation object)
    (normalForms : ∀ hub ∈ obstruction.demands,
      NormalForm object threshold hub)
    (cycleFree : ∀ hub ∈ obstruction.demands,
      TypeBDirectCycle.DirectCycleFree object order LengthOK packing hub) :
    GlobalLocalReflectionACE presentation object order LengthOK threshold
      dischargeScale piece assigned obstruction where
  contextualDyadicSafety := targetSafe
  centresIndependent := by
    intro left leftMem right rightMem different adjacent
    have rightHigh : IsHighCentre object threshold right :=
      obstruction.demands_high right rightMem
    have rightTight : object.degree right = threshold :=
      (normalForms left leftMem).neighbourTight adjacent
    exact (Nat.ne_of_gt rightHigh) rightTight
  neighbourTight := by
    intro hub hubMem vertex adjacent
    exact (normalForms hub hubMem).neighbourTight adjacent
  packedWindowCompatible := by
    intro hub _hubMem data eligible
    exact data.packedWindowIncidences_subset_localWindowBoundaryIncidences eligible
  directCycleFree := cycleFree
  replacementObstruction := by
    intro attempt _supportEq reducing
    exact attempt.route reducing
  minimalOverlap := obstruction.minimal

end

end TypeBRefinedSupport

end Hypostructure.Graph
