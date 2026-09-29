import Hypostructure.Graph.Statements.ColdMarkedGerm
import Hypostructure.Graph.Contracts.Spine.ColdSubcubicCharge
import Hypostructure.Graph.Contracts.Spine.ColdNeutral

/-!
# Contract: the marked neutral germ against `[157]`'s compression clause

`ColdMarkedGermUncompressedStatement`.  The marked germ is a germ of the
canonical extracted family, whose members are subcubic (F5) candidates of the
routed classification; so its support meets no heavy handoff centre.  With
`E = Q.toCanonical` (node `[166]`) its replacement is isomorphic to G, hence has
the vertex and edge count of G and is not strictly smaller.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

/-- A germ of the canonical extracted family has a subcubic support: it is
the incidence of a candidate occurrence, whose trace prefix (outside
occurrences) or support (cross-window occurrences) is subcubic. -/
theorem canonicalActiveColdGerm_support_subcubic (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object)
    (active : CanonicalActiveColdGerm data object germ) :
    ∀ vertex ∈ germ.support, object.degree vertex ≤ data.threshold := by
  classical
  obtain ⟨extraction, extEq, routing, occurrence, occMem, occEq⟩ := active
  obtain ⟨routing', witness⟩ := coldGermExtraction?_spec_of_eq_some data object extEq
  simp only [ColdGermFamilyWitness] at witness
  obtain ⟨_, _, _, ⟨subset, _, _⟩, _⟩ := witness
  have candidate : occurrence ∈ coldRoutedCandidates data object routing :=
    subset occMem
  unfold coldRoutedCandidates at candidate
  rw [Finset.mem_filter] at candidate
  rcases occurrence with epsilon | epsilon
  · obtain ⟨_, _, subcubic⟩ := candidate
    subst occEq
    let classified := coldRoutedClassified data object routing
    let germ := coldOccurrenceIncidence data object classified epsilon
    let corridor := coldOccurrenceCorridorAt data object classified epsilon
    let presentation := coldOccurrencePresentationAt data object classified epsilon
    let index := coldOccurrenceIndexAt data object classified epsilon
    have witness := (coldOccurrenceStateFacts data object classified epsilon).2.2.2
    have traceSpec := Classical.choose_spec
      (Graph.ColdCorridor.Corridor.FirstFailureGermWitness.exists_traceEnd
        (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
        (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
        corridor presentation index germ witness)
    intro vertex member
    exact subcubic vertex (traceSpec.2 member)
  · obtain ⟨_, subcubic⟩ := candidate
    subst occEq
    exact subcubic

/-- **Node `[157]`: the marked neutral germ is not handed off and its
replacement is not strictly smaller.** -/
theorem coldMarkedGermUncompressed_of_trivial (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (neutral : NeutralConfigurationStatement data object)
    (trivial : CanonicalReplacementTrivialStatement data object) :
    ColdMarkedGermUncompressedStatement data object := by
  classical
  obtain ⟨marked, markedEq, spec⟩ := markedNeutralGerm?_spec_of_neutral data object neutral
  obtain ⟨marked', markedEq', isTrivial⟩ := trivial
  have same : marked' = marked :=
    Option.some.inj (markedEq'.symm.trans markedEq)
  subst same
  have spec' := spec
  unfold MarkedNeutralGermSpec NeutralEqualLengthTerminalConfigurationAt at spec'
  obtain ⟨active, _reading, sizeEq, _canonical, _avoids⟩ := spec'
  have subcubic := canonicalActiveColdGerm_support_subcubic data object marked'.1 active
  have iso : (Graph.glue marked'.2.toPiece marked'.1.atom.outside).Isomorphic object := by
    have toCanon := marked'.1.piece.toCanonical_glue_isomorphic marked'.1.atom.outside
    rw [isTrivial]
    exact toCanon.trans ⟨marked'.1.atom.reconstructionIso⟩
  refine ⟨marked', markedEq', marked'.1.bounded, sizeEq, ?_,
    Graph.FiniteObject.vertexCount_eq_of_isomorphic iso,
    Graph.FiniteObject.edgeCount_eq_of_isomorphic iso, ?_⟩
  · rintro ⟨registry, ⟨centre, rfl, high⟩, notDisjoint⟩
    obtain ⟨vertex, vertexRegistry, vertexSupport⟩ := Finset.not_disjoint_iff.mp notDisjoint
    rw [Finset.mem_singleton] at vertexRegistry
    subst vertexRegistry
    exact absurd (subcubic _ vertexSupport) (Nat.not_le.mpr high)
  · exact Graph.FiniteObject.not_lexicographicallySmaller_of_isomorphic iso

open Classical in
/-- **F08 at the marked germ.**  `excision_dichotomy` at every path spanning the marked germ's
support, from the selection (no accepted cycle; minimality for the baseline). -/
theorem coldMarkedGermStretchExcision_of_neutral (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (neutral : NeutralConfigurationStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ X : Graph.FiniteObject.{u}, X.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold X →
      Graph.HasCycleWithLength data.LengthOK X) :
    ColdMarkedGermStretchExcisionStatement data object := by
  obtain ⟨marked, markedEq, _⟩ := markedNeutralGerm?_spec_of_neutral data object neutral
  refine ⟨marked, markedEq, ?_⟩
  intro a b p hp hlen _support
  exact Graph.SpliceLift.excision_dichotomy object p hp hlen
    (object.vertexFinset.filter (fun v => v ∈ Graph.SpliceLift.interior p))
    (fun v => by simp [Graph.FiniteObject.vertexFinset]) data.LengthOK avoids
    (Graph.MinimumDegreeAtLeast data.threshold)
    (fun X hb hs => minimal X hs hb)

/-- **The incidence structure of the marked germ's stretch.** -/
theorem coldMarkedGermStretchIncidence_of_neutral (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (neutral : NeutralConfigurationStatement data object)
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object) :
    ColdMarkedGermStretchIncidenceStatement data object := by
  classical
  obtain ⟨marked, markedEq, spec⟩ := markedNeutralGerm?_spec_of_neutral data object neutral
  refine ⟨marked, markedEq, ?_⟩
  have spec' := spec
  unfold MarkedNeutralGermSpec NeutralEqualLengthTerminalConfigurationAt at spec'
  obtain ⟨active, _⟩ := spec'
  have subcubic := canonicalActiveColdGerm_support_subcubic data object marked.1 active
  intro a b p hp hsupp i hi0 hilt
  have hmem : p.getVert i ∈ marked.1.support :=
    (hsupp _).1 (p.getVert_mem_support i)
  have hle := subcubic _ hmem
  have hge : data.threshold ≤ object.degree (p.getVert i) :=
    baseline.trans (Graph.FiniteObject.minDegree_le_degree object _)
  have hdeg : object.degree (p.getVert i) = data.threshold := le_antisymm hle hge
  refine ⟨hdeg, ?_⟩
  letI : FinEnum object.Vertex := object.vertices
  have hpred : object.graph.Adj (p.getVert i) (p.getVert (i - 1)) := by
    have := p.adj_getVert_succ (i := i - 1) (by omega)
    have e : i - 1 + 1 = i := by omega
    rw [e] at this
    exact this.symm
  have hsucc : object.graph.Adj (p.getVert i) (p.getVert (i + 1)) :=
    p.adj_getVert_succ (i := i) hilt
  have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro h
    have := hp.getVert_injOn (by simp; omega) (by simp; omega) h
    omega
  have hsub : ({p.getVert (i - 1), p.getVert (i + 1)} : Set object.Vertex) ⊆
      object.graph.neighborSet (p.getVert i) := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hpred
    · exact hsucc
  rw [Set.ncard_sdiff hsub (Set.toFinite _), ← Graph.FiniteObject.degree_eq_ncard_neighborSet,
    hdeg, Set.ncard_pair hne]

end Hypostructure.Graph.Contracts.Spine
