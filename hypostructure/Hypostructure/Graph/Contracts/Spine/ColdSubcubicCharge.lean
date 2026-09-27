import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.ColdCorridorTails

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

/-- **`lem:absorbed-germ-fan-data` (ii), the counted remainder core at `z`**
(tex 7926-7952; `lem:typeA-high-degree-handoff`, tex 11110-11131;
`def:decorated-fan-envelope`, tex 10898-10925; `lem:decorated-fan-admissibility`,
tex 11150-11158).

The paper's claim at G: for a selected half-edge `ε` of G outside node `[153]`'s
subcubic candidates, whose retained corridor first meets a vertex `z` of degree
above the baseline at index `i` (`firstIndex`), "the segments of the corridor on
either side of `z` are two connector tails separated at `z`, which is the
decorated handoff configuration of `lem:typeA-high-degree-handoff`".  That
configuration is an envelope `(Y, {z})` whose arms are the connector tails from
the two first neighbours of `z` "to their first-entry data in" the counted core
`Y`, with `Y ⊆ R` a connected `P₁₃`-free remainder core (`def:decorated-fan-envelope`)
and `z ∉ Y` ("the only new vertices counted outside `Y` are the decorations",
tex 11155).  So the claim needs a connected remainder core `Y ⊆ R(P₀)`, `z ∉ Y`,
which both corridor segments at `z` (`Corridor.entryTail` / `Corridor.exitTail`)
enter.

Recorded as an open construction (`lean-vs-paper-discrepancies.md#open-constructions`,
[177] tex:7932): in `lem:typeA-high-degree-handoff` the core is the Type A
support `X` the tails return to; a cold corridor has no such support.  Its two
segments at `z` run to the corridor's two boundary stubs, whose window endpoints
lie in ambient-cubic cold windows of `P₀`, outside `R`; nothing on G's ledger at
this node (the routed classification, `[10]`, the remainder normalization)
provides a connected remainder core avoiding `z` that both segments enter.
When `z` is the entry foot (`i = 0`) the entry-side segment is the stub `ε`
itself and enters no vertex of `R` at all: `coldAbsorbedRemainderCore_heavyEntryFoot`
proves, at G, that every selected half-edge with a heavy foot meets all the
hypotheses below at index `0` and falsifies the conclusion there. -/
theorem coldAbsorbedRemainderCore (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (_notCandidate : Sum.inl epsilon ∉ coldRoutedCandidates data object routing)
    (firstIndex : (coldOccurrenceCorridorAt data object
      (coldRoutedClassified data object routing) epsilon).Segment)
    (_firstBound : firstIndex.1 ≤ coldRoutedTraceEnd data object routing epsilon)
    (_high : data.threshold < object.degree
      ((coldOccurrenceCorridorAt data object
        (coldRoutedClassified data object routing) epsilon).head firstIndex))
    (_earlier : ∀ earlier : (coldOccurrenceCorridorAt data object
        (coldRoutedClassified data object routing) epsilon).Segment,
      earlier.1 < firstIndex.1 →
        object.degree ((coldOccurrenceCorridorAt data object
          (coldRoutedClassified data object routing) epsilon).head earlier) ≤
          data.threshold) :
    ∃ core : Finset object.Vertex,
      Graph.SupportComponents.Connected.ConnectedOn object core ∧
        core ⊆ object.remainderSupport (canonicalWindowPacking data object) ∧
        (coldOccurrenceCorridorAt data object
          (coldRoutedClassified data object routing) epsilon).head firstIndex ∉ core ∧
        (∃ vertex ∈ (coldOccurrenceCorridorAt data object
            (coldRoutedClassified data object routing) epsilon).entryTail firstIndex.1,
          vertex ∈ core) ∧
        ∃ vertex ∈ (coldOccurrenceCorridorAt data object
            (coldRoutedClassified data object routing) epsilon).exitTail firstIndex.1,
          vertex ∈ core := by
  -- OPEN-CONSTRUCTION [177] tex:7932 — see lean-vs-paper-discrepancies.md#open-constructions
  sorry

/-- **The obstruction to `[177]`'s core at G: the heavy entry foot.**

At G's retained classification (`K .coldFailureRouting`), let `ε` be a
selected half-edge of G whose outside endpoint (the foot of its corridor) has
degree above the baseline.  Then `ε` meets every hypothesis of
`coldAbsorbedRemainderCore` at `firstIndex = 0` -- it is not one of node
`[153]`'s subcubic candidates, index `0` is within the trace prefix, its head is
the heavy foot, and there is no earlier index -- and the hook's conclusion
fails there: the entry-side corridor segment at the foot is `[ε's window
endpoint]`, which lies in `X_cold ⊆ ⋃P₀` and so meets no subset of
`R(P₀)`.  Hence, at G, `coldAbsorbedRemainderCore` holds for such `ε` exactly
when G has no selected half-edge with a heavy foot; nothing on G's ledger at
`[177]` excludes one (`lean-vs-paper-discrepancies.md`, [177]). -/
theorem coldAbsorbedRemainderCore_heavyEntryFoot (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (heavyFoot : data.threshold < object.degree epsilon.1.2) :
    Sum.inl epsilon ∉ coldRoutedCandidates data object routing ∧
      ∃ firstIndex : (coldOccurrenceCorridorAt data object
          (coldRoutedClassified data object routing) epsilon).Segment,
        firstIndex.1 = 0 ∧
        firstIndex.1 ≤ coldRoutedTraceEnd data object routing epsilon ∧
        data.threshold < object.degree
          ((coldOccurrenceCorridorAt data object
            (coldRoutedClassified data object routing) epsilon).head firstIndex) ∧
        (∀ earlier : (coldOccurrenceCorridorAt data object
            (coldRoutedClassified data object routing) epsilon).Segment,
          earlier.1 < firstIndex.1 →
            object.degree ((coldOccurrenceCorridorAt data object
              (coldRoutedClassified data object routing) epsilon).head earlier) ≤
              data.threshold) ∧
        ¬ ∃ core : Finset object.Vertex,
          core ⊆ object.remainderSupport (canonicalWindowPacking data object) ∧
            ∃ vertex ∈ (coldOccurrenceCorridorAt data object
                (coldRoutedClassified data object routing) epsilon).entryTail
                  firstIndex.1,
              vertex ∈ core := by
  classical
  let classified := coldRoutedClassified data object routing
  let corridor := coldOccurrenceCorridorAt data object classified epsilon
  have stubEq : corridor.entryStub = (epsilon.1.2, epsilon.1.1) :=
    (coldOccurrenceStateFacts data object classified epsilon).2.1
  have footEq : corridor.head ⟨0, Nat.succ_pos _⟩ = epsilon.1.2 := by
    rw [← Graph.ColdCorridor.Corridor.vertexAt_eq_head,
      Graph.ColdCorridor.Corridor.vertexAt_zero, stubEq]
  refine ⟨?_, ⟨0, Nat.succ_pos _⟩, rfl, Nat.zero_le _, footEq ▸ heavyFoot,
    fun earlier before => absurd before (Nat.not_lt_zero _), ?_⟩
  · intro member
    simp only [coldRoutedCandidates, Finset.mem_filter, Finset.mem_univ,
      true_and] at member
    have footIn := Graph.ColdCorridor.Corridor.foot_mem_prefixSupport corridor
      (coldRoutedTraceEnd data object routing epsilon)
    rw [stubEq] at footIn
    exact absurd (member.2 _ footIn) (not_le.mpr heavyFoot)
  · rintro ⟨core, inside, meets⟩
    refine Graph.ColdCorridor.Corridor.entryTail_zero_not_meets corridor ?_ meets
    refine Finset.disjoint_left.mpr fun {vertex} inCore inWindows => ?_
    have notW := Graph.FiniteObject.notMem_windowSupport_of_mem_remainderSupport (inside inCore)
    obtain ⟨window, windowMem, vertexMem⟩ :=
      (Graph.ColdCorridor.mem_windowsOf object _ vertex).1 inWindows
    have packed : window ∈ canonicalWindowPacking data object :=
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp windowMem).1).1
    exact notW (Graph.FiniteObject.mem_windowSupport packed vertexMem)

end Hypostructure.Graph.Contracts.Spine
