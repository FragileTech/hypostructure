/-
fix2-348, second item: [144] step 2 (tex 5594/5614, 6026) with the [348]
fold analysis.  Scratch evidence, not part of the build.  Compile from
`hypostructure/` with `lake env lean <this file>`.

Setting at G's [144a] arm: the canonical support `Z` of the two same-token
pattern coordinates, readings `ρᵢ = retainedPiece G Z Xᵢ` (G's piece at `Z`,
edges inside `Xᵢ`), and the residual disjunct `ContextEquivalent ρ₁ ρ₂`.

(A) `representative_not_responsive_at_G`: at G, EVERY strictly smaller
    baseline representative `Z'` of `Z` (the fold of the admissible quotient
    included) fails the response clause of `ReplacementSupport` at G's own
    context `Y_G`: minimality puts an accepted cycle in `Z' ⊕ Y_G`, and
    `Z ⊕ Y_G ≅ G` has none.  So exit (c) at [144] can only be reached as a
    contradiction from `ContextEquivalent ρ₁ ρ₂`, i.e. through a Visibility
    statement: every accepted cycle of `Z' ⊕ Y_G` gives a context separating
    ρ₁ from ρ₂.
(B) `readings_not_contextEquivalent_of_spectra`: the part of that statement
    G's facts DO give: a label pair of `∂Z` joined in ρ₁ by a path of a length
    `a` that ρ₂ does not realize (for the chosen synthetic length `k`)
    refutes context equivalence at G (explicit synthetic path context; no
    internal accepted cycle in ρ₂ because ρ₂ ⊆ G).
(C) `readings_contextEquivalent_of_support_eq`: the configuration where it
    fails: equal declared supports (`X₁ = X₂`, `r_{π₁} ≠ r_{π₂}`) give equal
    readings, so the residual disjunct holds at G, no context separates them,
    and (A) refutes every representative: Visibility is false.
-/
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.GluedCrossingCycle

open Hypostructure Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

namespace F1Obstruction144

/-- (A) The response clause of `ReplacementSupport` fails at G's own context
for every smaller baseline representative of a connected proper support. -/
theorem representative_not_responsive_at_G
    {object : FiniteObject.{u}} {threshold : Nat} {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold representative →
      HasCycleWithLength LengthOK representative)
    {support : Finset object.Vertex}
    (connected : SupportComponents.Connected.ConnectedOn object support)
    (proper : ∃ vertex, vertex ∉ support)
    (representative : BoundaryPiece
      (SupportAtom.properAtom object support connected
        proper).decomposition.interface)
    (baseline : MinimumDegreeAtLeast threshold (glue representative
      (SupportAtom.properAtom object support connected
        proper).decomposition.outside))
    (smaller : (glue representative (SupportAtom.properAtom object support
      connected proper).decomposition.outside).LexicographicallySmaller object) :
    let atom := SupportAtom.properAtom object support connected proper
    ¬ (HasCycleWithLength LengthOK (glue representative atom.decomposition.outside) →
        HasCycleWithLength LengthOK
          (glue atom.decomposition.piece atom.decomposition.outside)) := by
  intro atom transfer
  exact avoids (((cycleTargetInterface LengthOK).isomorphismInvariant.iff_of_iso
    ⟨atom.decomposition.reconstructionIso⟩).mp
      (transfer (minimality _ smaller baseline)))

/-- A reading of G's piece carries no accepted cycle of its own. -/
theorem reading_safe {object : FiniteObject.{u}} {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (support retained : Finset object.Vertex) :
    ¬ ∃ (pieceBase : (SupportAtom.boundary object support).Vertex ⊕
          (SupportAtom.retainedPiece object support retained).Internal)
        (lifted : (SupportAtom.retainedPiece object support retained).graph.Walk
          pieceBase pieceBase),
        lifted.IsCycle ∧ LengthOK lifted.length := by
  rintro ⟨pieceBase, lifted, liftedCycle, lengthOk⟩
  refine not_target_retainedGlue avoids support retained
    ⟨⟨_, lifted.map (pieceHom (SupportAtom.retainedPiece object support retained)
      (SupportAtom.outside object support)), ?_, ?_⟩⟩
  · exact liftedCycle.map (pieceEmbedding _ _).injective
  · rw [SimpleGraph.Walk.length_map]
    exact lengthOk

/-- (B) Spectral separation of G's two readings refutes their context
equivalence at G. -/
theorem readings_not_contextEquivalent_of_spectra
    {object : FiniteObject.{u}} {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (support first second : Finset object.Vertex)
    {left right : (SupportAtom.boundary object support).Vertex}
    (distinct : left ≠ right) {k : Nat} (kPos : 1 ≤ k)
    (firstPath : ∃ q : (SupportAtom.retainedPiece object support first).graph.Walk
        (.inl left) (.inl right), q.IsPath ∧ LengthOK (q.length + (k + 1)))
    (secondSpectrum : ¬ ∃ q : (SupportAtom.retainedPiece object support
        second).graph.Walk (.inl left) (.inl right),
        q.IsPath ∧ LengthOK (q.length + (k + 1))) :
    ¬ Response.ContextEquivalent (HasCycleWithLength LengthOK)
        (SupportAtom.retainedPiece object support first)
        (SupportAtom.retainedPiece object support second) := by
  intro equivalent
  obtain ⟨outside, differs⟩ :=
    PathContext.targetDefect_of_spectra distinct kPos firstPath
      (reading_safe avoids support second) secondSpectrum
  exact differs (equivalent outside)

/-- (C) Equal declared supports give equal readings: the residual disjunct
holds and no context separates the two coordinates. -/
theorem readings_contextEquivalent_of_support_eq
    {object : FiniteObject.{u}} {LengthOK : Nat → Prop}
    (support first second : Finset object.Vertex) (same : first = second) :
    Response.ContextEquivalent (HasCycleWithLength LengthOK)
        (SupportAtom.retainedPiece object support first)
        (SupportAtom.retainedPiece object support second) := by
  subst same
  exact fun _ => Iff.rfl

end F1Obstruction144

#print axioms F1Obstruction144.representative_not_responsive_at_G
#print axioms F1Obstruction144.readings_not_contextEquivalent_of_spectra
#print axioms F1Obstruction144.readings_contextEquivalent_of_support_eq

/-!
## Follow-up: the compression candidate from equal spectra (both [144] and [348])

Every representative `Z'` of a connected proper support `S` of G is either
* a SUBGRAPH of G's piece at `S` (same vertices, fewer edges -- e.g. "replace
  ρ₁ by ρ₂", i.e. delete the edges of `X₁` not in `X₂`; or at [348] the core
  restriction's `retainedBasinPiece`): then the response clause holds in EVERY
  context for free (`subgraph_response`), so no equivalence of readings is
  used, and G itself refutes `baseline ∧ smaller` for it
  (`subgraph_not_baseline_and_smaller`); or
* not a subgraph: then (A) refutes the response clause at `Y_G` whenever
  baseline and smaller hold.
So no clause of `ReplacementSupport`/`CompressibleSupport` reads the
context equivalence ρ₁ ~ ρ₂ (or, at [348], the core equivalence
`ρ|_{C_ess} ~ ρ`): these relate two readings, never G's piece and a smaller
piece.  Equal path/linkage spectra of two readings build no compression.
-/

namespace F1Obstruction144

/-- A subgraph of G's piece at `S` passes the response clause against every
context. -/
theorem subgraph_response {object : FiniteObject.{u}} {LengthOK : Nat → Prop}
    (support : Finset object.Vertex)
    (smaller : SimpleGraph ((SupportAtom.boundary object support).Vertex ⊕
      (SupportAtom.piece object support).Internal))
    (decide : DecidableRel smaller.Adj)
    (le : smaller ≤ (SupportAtom.piece object support).graph)
    (outside : OutsideContext (SupportAtom.boundary object support))
    (cycle : HasCycleWithLength LengthOK
      (glue { SupportAtom.piece object support with
        graph := smaller, decideAdj := decide } outside)) :
    HasCycleWithLength LengthOK (glue (SupportAtom.piece object support) outside) :=
  hasCycleWithLength_of_hom
    (left := glue { SupportAtom.piece object support with
      graph := smaller, decideAdj := decide } outside)
    (right := glue (SupportAtom.piece object support) outside)
    (SimpleGraph.Hom.ofLE (glueGraph_mono outside smaller decide le))
    (fun _ _ equal => equal) cycle

/-- At G no subgraph representative of any support keeps the baseline and is
strictly smaller: minimality would give it an accepted cycle, which maps into
G. -/
theorem subgraph_not_baseline_and_smaller {object : FiniteObject.{u}}
    {threshold : Nat} {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold representative →
      HasCycleWithLength LengthOK representative)
    (support : Finset object.Vertex)
    (smaller : SimpleGraph ((SupportAtom.boundary object support).Vertex ⊕
      (SupportAtom.piece object support).Internal))
    (decide : DecidableRel smaller.Adj)
    (le : smaller ≤ (SupportAtom.piece object support).graph) :
    let replacement := { SupportAtom.piece object support with
      graph := smaller, decideAdj := decide }
    ¬ (MinimumDegreeAtLeast threshold
          (glue replacement (SupportAtom.outside object support)) ∧
        (glue replacement (SupportAtom.outside object support)).LexicographicallySmaller
          object) := by
  intro replacement ⟨baseline, lex⟩
  have pieceCycle := subgraph_response support smaller decide le
    (SupportAtom.outside object support) (minimality _ lex baseline)
  let iso := (SupportAtom.decomposition object support).reconstructionIso
  exact avoids (hasCycleWithLength_of_hom iso.toHom iso.injective pieceCycle)

end F1Obstruction144

#print axioms F1Obstruction144.subgraph_response
#print axioms F1Obstruction144.subgraph_not_baseline_and_smaller
