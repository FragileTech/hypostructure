import Hypostructure.Graph.Statements.Spine

/-!
# Contract: the full charge of a subcubic cold half-edge (`[153]`, `[175]`)

`lem:absorbed-germ-fan-data` (i), tex 7920-7922: *"`J` contains no vertex of
degree at least `4`.  Then `J` is subcubic, the count of
`lem:cold-germ-extraction` charges `ε` in full"* -- together with
`lem:cold-germ-extraction` (tex 7318-7322: after deleting the already routed
handoff incidences, *"each remaining selected half-edge supplies one canonical
first-failure cold bounded configuration"*).  On the routed cold residual the
first failure of every selected half-edge is (F5) or (F4)
(`ColdSurvivingFirstFailureStatement`); a half-edge whose bounded
first-failure prefix is subcubic is charged in full as an (F5) candidate.

The (F4) registry `ColdDeclaredHandoffSupport` is G's heavy handoff centres
(user-approved repair, `lean-vs-paper-discrepancies.md`, "(F4) registry: the
heavy handoff centres"; tex 7326-7329, 7926-7930).  An (F4) first failure then
precedes the germ segment, whose head lies in the germ support, which the trace
prefix covers; so the trace prefix contains the heavy centre and is not
subcubic.  All facts below are instantiated at the retained classification of
G published by `K .coldFailureRouting`.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

/-- G's (F4) registry is a heavy registry: every vertex of a declared handoff
support of G has degree above the baseline. -/
theorem coldDeclaredHandoffSupport_registryHigh (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Graph.ColdCorridor.Corridor.RegistryHigh data.threshold
      (ColdDeclaredHandoffSupport data object) := by
  rintro support ⟨centre, rfl, high⟩ vertex member
  rw [Finset.mem_singleton] at member
  subst member
  exact high

/-- The germ event of the retained (F5) witness: some segment satisfies
`ColdFirstFailureGermAt`, and its head lies in the germ support. -/
theorem coldGermAt_exists_head_mem (data : Parameters)
    {object : Graph.FiniteObject.{u}} {windows component : Finset object.Vertex}
    (corridor : Graph.ColdCorridor.Corridor object windows component)
    (presentation : Graph.ColdCorridor.Presentation data.coldSignature object)
    (index : corridor.Segment → presentation.Segment)
    (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object)
    (witness : corridor.FirstFailureGermWitness
      (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
      (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
      presentation index germ) :
    ∃ g : corridor.Segment,
      ColdFirstFailureGermAt data object corridor presentation index germ g ∧
        corridor.head g ∈ germ.support := by
  rcases witness.2.2 with terminal | repeated
  · refine ⟨⟨corridor.inside.1.length, Nat.lt_succ_self _⟩,
      Or.inl ⟨terminal.1, terminal.2.1, terminal.2.2, rfl⟩, ?_⟩
    rw [terminal.2.1]
    exact Graph.ColdCorridor.Corridor.head_terminal_mem_prefixSupport_statesRead
      corridor
  · obtain ⟨left, right, rightBound, before, same, readings, first,
      supportEq, leftRecord, rightRecord⟩ := repeated
    refine ⟨right, Or.inr ⟨left, right, rightBound, before, same, readings,
      first, supportEq, leftRecord, rightRecord, rfl⟩, ?_⟩
    rw [supportEq]
    exact Graph.ColdCorridor.Corridor.head_right_mem_intervalSupport corridor
      left right (Nat.le_of_lt before)

/-- **An (F4)-routed half-edge of G has a non-subcubic trace.**  At the
retained classification of `K .coldFailureRouting`: if the first failure of
`ε` is (F4), the trace prefix `coldRoutedTraceEnd` contains a vertex above the
baseline (the heavy centre the corridor first enters). -/
theorem coldHandoffOccurrence_not_subcubic (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (handoff : ColdFirstFailureHandoffOccurrence data object
      (coldRoutedClassified data object routing) epsilon) :
    ¬ ∀ vertex ∈
        (coldOccurrenceCorridorAt data object
          (coldRoutedClassified data object routing) epsilon).prefixSupport
          (coldRoutedTraceEnd data object routing epsilon),
        object.degree vertex ≤ data.threshold := by
  classical
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
  obtain ⟨g, germAt, gMem⟩ :=
    coldGermAt_exists_head_mem data corridor presentation index germ witness
  obtain ⟨first, handoffAt, minimal⟩ := handoff
  have firstLe : first.1 ≤ g.1 := by
    by_contra after
    exact minimal g (lt_of_not_ge after) (.germ germAt)
  exact Graph.ColdCorridor.Corridor.handoff_before_germ_not_subcubic corridor
    data.threshold (coldRoutedTraceEnd data object routing epsilon) germ.support
    traceSpec.2 g gMem (coldDeclaredHandoffSupport_registryHigh data object)
    first firstLe handoffAt

/-- **`lem:absorbed-germ-fan-data` (i)**: a selected half-edge of G whose
bounded first-failure prefix is subcubic is an (F5) configuration of the
routed classification, not an (F4) handoff. -/
theorem coldSubcubicFirstFailureGerm (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (subcubic : ∀ vertex ∈
        (coldOccurrenceCorridorAt data object
          (coldRoutedClassified data object routing) epsilon).prefixSupport
          (coldRoutedTraceEnd data object routing epsilon),
        object.degree vertex ≤ data.threshold) :
    ColdFirstFailureGermOccurrence data object
      (coldRoutedClassified data object routing) epsilon := by
  rcases Classical.choose_spec routing.surviving.holds epsilon with germ | handoff
  · exact germ
  · exact (coldHandoffOccurrence_not_subcubic data object routing epsilon
      handoff subcubic).elim

/-- **`lem:absorbed-germ-fan-data` (ii), the counted core** (tex 7926-7934,
with `def:decorated-fan-envelope`, tex 10898-10903): for a selected half-edge `ε`
of G outside node `[153]`'s candidate set, its first-failure support `J` -- the
prefix of G's retained corridor for `ε` through its trace end -- is the core of
the decorated handoff envelope at the heavy centre, hence a remainder core
`Y ⊆ R = G − ⋃P₀`.

Recorded as a paper error (`lean-vs-paper-discrepancies.md#paper-errors`,
[177] tex:7932): the corridor lives in `G − X_cold`, which keeps the hot and
non-ambient-cubic cold windows of `P₀`, so `J` may meet `⋃P₀` before its heavy
centre; the paper never shows `J ⊆ R`, which the envelope's core requires. -/
theorem coldAbsorbedPrefix_subset_remainder (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (_notCandidate : Sum.inl epsilon ∉ coldRoutedCandidates data object routing) :
    (coldOccurrenceCorridorAt data object
        (coldRoutedClassified data object routing) epsilon).prefixSupport
        (coldRoutedTraceEnd data object routing epsilon) ⊆
      object.remainderSupport (canonicalWindowPacking data object) := by
  -- PAPER-ERROR [177] tex:7932 — see lean-vs-paper-discrepancies.md#paper-errors
  sorry

end Hypostructure.Graph.Contracts.Spine
