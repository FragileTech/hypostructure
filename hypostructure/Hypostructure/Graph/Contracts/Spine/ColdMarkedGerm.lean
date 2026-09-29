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

end Hypostructure.Graph.Contracts.Spine
