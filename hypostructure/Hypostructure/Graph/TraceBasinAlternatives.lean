import Hypostructure.Graph.ResponseDelocalization
import Hypostructure.Graph.GluedCycleSides
import Hypostructure.Graph.ExitFourFamily

/-!
# The failure alternatives of a trace basin

`def:typeA-trace-basin`: the trace basin `B_u` is *target-complete-minimal*
when none of four alternatives occurs.  Each alternative below is the
manuscript's own clause, stated on the declared `u`-supported coordinate
algebra `ρ_u(B_u)` of the selected basin (`PresentedEntry.ofTraceBasin`):

* (a) a trace-local quotient of `ρ_u(B_u)` is distinguished by an outside
  context — `Response.TargetDefect` of a retained reading against the basin;
* (b) a nontrivial target-complete response quotient of the declared
  trace-response state — `TraceResponseQuotient` of
  `Graph/Route8Residual.lean`;
* (c) an equality among coordinates of `ρ_u(B_u)` becomes target-complete only
  after adjoining a larger connected support `Z ⊋ B_u` — `Route8.Delocalization`
  based at the basin;
* (d) two declared outside connector configurations of `ρ_u(B_u)`, through the
  receiver's completion port, have a surviving first separator in the sense of
  `def:typeA-continuation-classes` — `DecoratedHandoff.Surviving`.

`lem:typeA-reduced-silent-residual` identifies (a)--(d) with exits (4)--(7) of
`def:typeA-saturated-exits`; the predicates here are therefore the same data the
saturated-exit decisions of the Type A branch test, read at one basin.  Nothing
here is specialized to a manuscript constant.
-/

namespace Hypostructure.Graph.Route8.TraceBasin

open Hypostructure
open Hypostructure.Graph

universe u

/-- **Alternative (a) of `def:typeA-trace-basin`.**  A trace-local quotient of
`ρ_u(B_u)` — retaining a subset of the declared family and forgetting a
coordinate with genuinely internal declared support — whose reading some
outside `∂B_u`-context distinguishes from the basin itself. -/
def TraceLocalTargetDefect (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (basin : Finset object.Vertex) : Prop :=
  ∃ retained : Finset (PresentedEntry.TraceCoordinate object support),
    retained ⊆ PresentedEntry.traceCoordinates object support threshold receiver load ∧
      (∃ changed ∈ PresentedEntry.traceCoordinates object support threshold receiver load,
        changed ∉ retained ∧
          ExitFour.TraceCoordinateInternal object support basin threshold receiver
            load changed) ∧
      Response.TargetDefect (HasCycleWithLength LengthOK)
        (PresentedEntry.retainedReading object support basin threshold LengthOK
          (PresentedEntry.retainedBaseCoordinates object support retained))
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin)

/-- **Alternative (c) of `def:typeA-trace-basin`.**  An equality among declared
coordinates of `ρ_u(B_u)` that becomes target-complete only after adjoining a
larger connected support `Z ⊋ B_u`: `Route8.Delocalization` of the basin's own
presented entry, based at the basin. -/
def TraceDelocalization (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (basin : Finset object.Vertex) : Prop :=
  Nonempty
    (Delocalization (MinimumDegreeAtLeast threshold) (HasCycleWithLength LengthOK)
      (PresentedEntry.ofTraceBasin object support basin threshold LengthOK receiver
        load)
      basin)

/-- **Alternative (d) of `def:typeA-trace-basin`.**  Two declared outside
connector configurations of `ρ_u(B_u)` through the receiver's completion port —
two routed loads of the finite connector family, one of them the indexed load —
separate at a first separator `z`, and the identification on the switch support
`S_z` is neither target-defective, nor target-complete, nor valid only after
enlarging: `z` is surviving. -/
def TraceSurvivingSeparator (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (_basin : Finset object.Vertex) : Prop :=
  ∃ family : ExitFour.ContinuationFamily object support threshold receiver,
    load ∈ family.loads ∧
      ∃ leftLoad rightLoad : object.Vertex,
        ∃ leftMem : leftLoad ∈ family.loads, ∃ rightMem : rightLoad ∈ family.loads,
          leftLoad ≠ rightLoad ∧
            ∃ separation : DecoratedHandoff.Separation object support receiver
                family.outside,
              separation.left.path = (family.germ leftLoad leftMem).path ∧
                separation.right.path = (family.germ rightLoad rightMem).path ∧
                ∃ reading : DecoratedHandoff.SwitchReading separation,
                  DecoratedHandoff.Surviving (HasCycleWithLength LengthOK) reading
                    (∃ representative : FiniteObject.{u},
                      representative.LexicographicallySmaller object ∧
                        MinimumDegreeAtLeast threshold representative ∧
                        (HasCycleWithLength LengthOK representative →
                          HasCycleWithLength LengthOK object))

/-- The selected basin is target-complete-minimal precisely when none of the
four trace-local failure alternatives of `def:typeA-trace-basin` occurs. -/
def TargetCompleteMinimal (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (basin : Finset object.Vertex) : Prop :=
  TraceComplete object support threshold receiver load basin ∧
    ¬ TraceLocalTargetDefect object support threshold LengthOK receiver load basin ∧
    (¬ ∃ retained,
      TraceResponseQuotient object support threshold LengthOK receiver load basin
        retained) ∧
    ¬ TraceDelocalization object support threshold LengthOK receiver load basin ∧
    ¬ TraceSurvivingSeparator object support threshold LengthOK receiver load basin

/-- The concrete route-8 entry of `def:typeA-route8-carriers` for the selected
load/basin. -/
def Route8Entry (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex) : Prop :=
  ∃ basin : Finset object.Vertex,
    select? object support threshold receiver load = some basin ∧
      TargetCompleteMinimal object support threshold LengthOK receiver load basin

/-- **Alternative (c) is refuted by the standing invariants** —
`lem:proper-smearing` and `lem:no-silent-global-smearing` through
`DeclaredQuotient.localize`: the delocalization's admissible quotient carries
its representative, a replacement of the proper enlarging support — forbidden
by `K .replacementExclusion` — or a strictly smaller admissible closed
representative — forbidden by the selection's own minimality and target
avoidance. -/
theorem not_traceDelocalization {object : FiniteObject.{u}}
    {support : Finset object.Vertex} {threshold : Nat} {LengthOK : Nat → Prop}
    {receiver load : object.Vertex} {basin : Finset object.Vertex}
    (exclusion : ∀ enlarged : Finset object.Vertex,
      ¬ Strategy.InterfaceReplacement.ReplacementSupport
          (MinimumDegreeAtLeast threshold) (HasCycleWithLength LengthOK) object
          enlarged)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold representative →
      HasCycleWithLength LengthOK representative) :
    ¬ TraceDelocalization object support threshold LengthOK receiver load
      basin := by
  rintro ⟨delocalization⟩
  rcases delocalization.localize with replacement |
    ⟨representative, smaller, baseline, transfer⟩
  · exact exclusion _ replacement
  · exact avoids (transfer (minimality representative smaller baseline))

/-- **Alternative (a) supplies the exit-(4) witness** — the trace-local
target-defective quotient is a member of the canonical family of type (Q3),
and its declared support contains the selected load. -/
theorem exists_witness_of_traceLocalTargetDefect {object : FiniteObject.{u}}
    {support : Finset object.Vertex} {threshold scale : Nat}
    {LengthOK : Nat → Prop} {receiver load : object.Vertex}
    {basin : Finset object.Vertex}
    (selected : select? object support threshold receiver load = some basin)
    (loadRouted : load ∈ object.routedLoads support threshold receiver)
    (defect : TraceLocalTargetDefect object support threshold LengthOK receiver
      load basin) :
    ∃ witness : ExitFour.Witness (HasCycleWithLength LengthOK) support
        threshold scale receiver ∅,
      witness.load = load := by
  classical
  obtain ⟨retained, retainedSubset, nontrivial, targetDefect⟩ := defect
  refine ⟨⟨load, ?_, .q3
    { LengthOK := LengthOK
      target_eq := rfl
      basin := basin
      selected := selected
      retained := retained
      retained_subset := retainedSubset
      nontrivial := nontrivial
      targetDefect := targetDefect }⟩, rfl⟩
  rw [ExitFour.mem_unpeeledLoads]
  exact ⟨loadRouted, Finset.notMem_empty load⟩

/-- **`lem:typeA-pressure-token-two-carriers`** — alternative (a)'s
distinguishing data yield a demand token whose witnessing accepted event
records two distinct cut-boundary labels of the basin.  The one-sided
monotone transfer pins the realizing side to the basin's full piece
(`exists_context_of_not_contextEquivalent`); the witnessing cycle must enter
the basin, since the label-edge-preserving retained restriction would
otherwise realize the target and contradict the defect
(`hasCycleWithLength_restriction_of_avoids_piece_internal` +
`glue_swap_target_iff`); and the glued-cycle classification then yields the
two labels — a piece lift would decode to an accepted ambient cycle against
the standing avoidance. -/
theorem exists_two_cutBoundary_of_traceLocalTargetDefect
    {object : FiniteObject.{u}} {support : Finset object.Vertex}
    {threshold : Nat} {LengthOK : Nat → Prop}
    {receiver load : object.Vertex} {basin : Finset object.Vertex}
    (defect : TraceLocalTargetDefect object support threshold LengthOK
      receiver load basin)
    (avoids : ¬ HasCycleWithLength LengthOK object) :
    ∃ (context : OutsideContext
        (Strategy.InterfaceReplacement.SupportAtom.boundary object basin))
      (certificate : CycleCertificate
        (glue (Strategy.InterfaceReplacement.SupportAtom.piece object basin)
          context) LengthOK)
      (left right : (Strategy.InterfaceReplacement.SupportAtom.boundary object
        basin).Vertex),
      left ≠ right ∧
        Sum.inl left ∈ certificate.walk.support ∧
        Sum.inl right ∈ certificate.walk.support := by
  classical
  obtain ⟨retained, _retainedSubset, _nontrivial, targetDefect⟩ := defect
  have monotone : ∀ outsideCtx : OutsideContext
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin),
      HasCycleWithLength LengthOK
        (glue (PresentedEntry.retainedReading object support basin threshold
          LengthOK (PresentedEntry.retainedBaseCoordinates object support
            retained)) outsideCtx) →
      HasCycleWithLength LengthOK
        (glue (Strategy.InterfaceReplacement.SupportAtom.piece object basin)
          outsideCtx) := fun outsideCtx =>
    PresentedEntry.hasCycleWithLength_glue_of_retainedReading object support
      basin threshold LengthOK
      (PresentedEntry.retainedBaseCoordinates object support retained)
      outsideCtx
  have failure : ¬ Response.ContextEquivalent (HasCycleWithLength LengthOK)
      (PresentedEntry.retainedReading object support basin threshold LengthOK
        (PresentedEntry.retainedBaseCoordinates object support retained))
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin) := by
    obtain ⟨distinguishing, distinguishes⟩ := targetDefect
    exact fun equivalent => distinguishes (equivalent distinguishing)
  obtain ⟨context, acceptedPiece, notReading⟩ :=
    Response.exists_context_of_not_contextEquivalent monotone failure
  obtain ⟨certificate⟩ := acceptedPiece
  refine ⟨context, certificate, ?_⟩
  by_cases meetsPiece : ∃ inner, (Sum.inr (Sum.inl inner) :
      GluedVertex (Strategy.InterfaceReplacement.SupportAtom.piece object
        basin) context) ∈ certificate.walk.support
  · obtain ⟨pieceInner, pieceInnerMem⟩ := meetsPiece
    rcases GluedCycleSides.cycle_pieceLift_or_contextInternal_or_labelDart
        (c := certificate.walk) certificate.isCycle with
      ⟨pieceBase, lifted, liftedCycle, liftedLength⟩ |
        ⟨contextInner, contextInnerMem⟩ |
        ⟨left, right, distinct, leftMem, rightMem, _contextAdj, _dartEdge⟩
    · exfalso
      refine avoids ⟨⟨_, lifted.map
        ⟨Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin,
          fun adjacent => adjacent⟩, ?_, ?_⟩⟩
      · exact liftedCycle.map
          (PresentedEntry.retainedBasinPiece_decode_injective object basin)
      · rw [SimpleGraph.Walk.length_map]
        exact (congrArg LengthOK liftedLength).mpr certificate.length_ok
    · obtain ⟨left, right, distinct, leftMem, rightMem⟩ :=
        GluedCycleSides.exists_two_labels_of_cycle_sides certificate.isCycle
          pieceInnerMem contextInnerMem
      exact ⟨left, right, distinct, leftMem, rightMem⟩
    · exact ⟨left, right, distinct, leftMem, rightMem⟩
  · exfalso
    push_neg at meetsPiece
    have transferred :=
      GluedCycleSides.hasCycleWithLength_restriction_of_avoids_piece_internal
        (piece := Strategy.InterfaceReplacement.SupportAtom.piece object basin)
        (outside := context)
        (PresentedEntry.retainedBasinPiece object basin
          (PresentedEntry.retainedVertices object support
            (PresentedEntry.retainedBaseCoordinates object support
              retained))).graph
        (PresentedEntry.retainedBasinPiece object basin
          (PresentedEntry.retainedVertices object support
            (PresentedEntry.retainedBaseCoordinates object support
              retained))).decideAdj
        (fun label other adjacent =>
          PresentedEntry.retainedBasinPiece_adj_of_label object basin _
            label other adjacent)
        certificate.isCycle certificate.length_ok
        (fun inner member => meetsPiece inner member)
    have retainedGlue : HasCycleWithLength LengthOK
        (glue (PresentedEntry.retainedBasinPiece object basin
          (PresentedEntry.retainedVertices object support
            (PresentedEntry.retainedBaseCoordinates object support retained)))
          context) := transferred
    exact notReading ((CanonicalPiece.glue_swap_target_iff
      (minimumDegreeAtLeast_isomorphismInvariant threshold)
      (cycleTargetInterface LengthOK).isomorphismInvariant
      (PresentedEntry.retainedBasinPiece object basin
        (PresentedEntry.retainedVertices object support
          (PresentedEntry.retainedBaseCoordinates object support retained)))
      context).mpr retainedGlue)

/-- **`def:typeA-two-terminal-pressure-records`** — the canonical demand
record at a selected basin: an *actual two-terminal record* (an accepted
event of the basin glued to its actual exterior, with an outside corridor
between two distinct cut-boundary labels along event edges, every interior
vertex context-internal), or a *profile record* (an accepted event of the
basin glued to a distinguished non-actual context, with two distinct visited
labels).  `lem:typeA-pressure-records-canonical`: the two record classes are
disjoint by the context-equality polarity. -/
def CanonicalDemandRecord (object : FiniteObject.{u})
    (basin : Finset object.Vertex) (LengthOK : Nat → Prop) : Prop :=
    (∃ certificate : CycleCertificate
        (glue (Strategy.InterfaceReplacement.SupportAtom.piece object basin)
          (Strategy.InterfaceReplacement.SupportAtom.outside object basin))
        LengthOK,
      ∃ left right : (Strategy.InterfaceReplacement.SupportAtom.boundary
          object basin).Vertex,
        left ≠ right ∧
          ∃ corridor : (glueGraph
              (Strategy.InterfaceReplacement.SupportAtom.piece object basin)
              (Strategy.InterfaceReplacement.SupportAtom.outside object
                basin)).Walk (.inl left) (.inl right),
            corridor.edges ⊆ certificate.walk.edges ∧
              ∀ x ∈ corridor.support,
                x = Sum.inl left ∨ x = Sum.inl right ∨
                  ∃ inner, x = Sum.inr (Sum.inr inner)) ∨
    (∃ context : OutsideContext
        (Strategy.InterfaceReplacement.SupportAtom.boundary object basin),
      context ≠ Strategy.InterfaceReplacement.SupportAtom.outside object
          basin ∧
        ∃ certificate : CycleCertificate
            (glue (Strategy.InterfaceReplacement.SupportAtom.piece object
              basin) context) LengthOK,
          ∃ left right : (Strategy.InterfaceReplacement.SupportAtom.boundary
              object basin).Vertex,
            left ≠ right ∧
              Sum.inl left ∈ certificate.walk.support ∧
              Sum.inl right ∈ certificate.walk.support)

/-- **`lem:typeA-pressure-records-canonical`** — every target-defect entry
carries its canonical demand record: the distinguishing context is the actual
exterior (actual record, with the corridor supplied by the glued-cycle
classification — the piece lift decodes to an accepted ambient cycle against
the standing avoidance, the context-internal visit yields the corridor, and
the label dart is itself a one-edge corridor) or it is not (profile record).
The manuscript's lexicographically-first choices are replaced by classical
witnesses, as everywhere in this lane. -/
theorem exists_record_of_traceLocalTargetDefect
    {object : FiniteObject.{u}} {support : Finset object.Vertex}
    {threshold : Nat} {LengthOK : Nat → Prop}
    {receiver load : object.Vertex} {basin : Finset object.Vertex}
    (defect : TraceLocalTargetDefect object support threshold LengthOK
      receiver load basin)
    (avoids : ¬ HasCycleWithLength LengthOK object) :
    CanonicalDemandRecord object basin LengthOK := by
  classical
  unfold CanonicalDemandRecord
  obtain ⟨context, certificate, left, right, distinct, leftMem, rightMem⟩ :=
    exists_two_cutBoundary_of_traceLocalTargetDefect defect avoids
  by_cases actual : context =
      Strategy.InterfaceReplacement.SupportAtom.outside object basin
  · subst actual
    refine Or.inl ⟨certificate, ?_⟩
    rcases GluedCycleSides.cycle_pieceLift_or_contextInternal_or_labelDart
        (c := certificate.walk) certificate.isCycle with
      ⟨pieceBase, lifted, liftedCycle, liftedLength⟩ |
        ⟨contextInner, contextInnerMem⟩ |
        ⟨dartLeft, dartRight, dartDistinct, _dartLeftMem, _dartRightMem,
          dartAdj, dartEdge⟩
    · exfalso
      refine avoids ⟨⟨_, lifted.map
        ⟨Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin,
          fun adjacent => adjacent⟩, ?_, ?_⟩⟩
      · exact liftedCycle.map
          (PresentedEntry.retainedBasinPiece_decode_injective object basin)
      · rw [SimpleGraph.Walk.length_map]
        exact (congrArg LengthOK liftedLength).mpr certificate.length_ok
    · exact GluedCycleSides.exists_corridor_of_cycle_contextInternal
        certificate.isCycle contextInnerMem distinct leftMem rightMem
    · have dartGlueAdj : (glueGraph
          (Strategy.InterfaceReplacement.SupportAtom.piece object basin)
          (Strategy.InterfaceReplacement.SupportAtom.outside object
            basin)).Adj (.inl dartLeft) (.inl dartRight) := by
        refine (glueGraph_adj_iff _ _ _ _).mpr (Or.inr ⟨.inl dartLeft,
          .inl dartRight, dartAdj, ?_, ?_⟩) <;> rfl
      refine ⟨dartLeft, dartRight, dartDistinct,
        SimpleGraph.Walk.cons dartGlueAdj SimpleGraph.Walk.nil, ?_, ?_⟩
      · intro e emem
        rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil] at emem
        rw [List.mem_singleton.mp emem]
        exact dartEdge
      · intro x xmem
        rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
          at xmem
        rcases List.mem_cons.mp xmem with rfl | tailmem
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (List.mem_singleton.mp tailmem))
  · exact Or.inr ⟨context, actual, certificate, left, right, distinct,
      leftMem, rightMem⟩

/-- **Target-complete-minimality from the branch's refutations**: the selected
basin is trace-complete, and each of the four failure alternatives is refuted
— (a), (b), and (d) by hypothesis (the quotient alternative is cased on the
branch, exactly as the exit-`(5)` decision cases its realized datum; it is
never refuted from the standing invariants), and (c) through
`not_traceDelocalization`. -/
theorem targetCompleteMinimal_of_refutations {object : FiniteObject.{u}}
    {support : Finset object.Vertex} {threshold : Nat} {LengthOK : Nat → Prop}
    {receiver load : object.Vertex} {basin : Finset object.Vertex}
    (complete : TraceComplete object support threshold receiver load basin)
    (noDefect : ¬ TraceLocalTargetDefect object support threshold LengthOK
      receiver load basin)
    (noQuotient : ¬ ∃ retained,
      TraceResponseQuotient object support threshold LengthOK receiver load
        basin retained)
    (exclusion : ∀ enlarged : Finset object.Vertex,
      ¬ Strategy.InterfaceReplacement.ReplacementSupport
          (MinimumDegreeAtLeast threshold) (HasCycleWithLength LengthOK) object
          enlarged)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold representative →
      HasCycleWithLength LengthOK representative)
    (noSeparator : ¬ TraceSurvivingSeparator object support threshold LengthOK
      receiver load basin) :
    TargetCompleteMinimal object support threshold LengthOK receiver load
      basin := by
  refine ⟨complete, noDefect, noQuotient, ?_, noSeparator⟩
  exact not_traceDelocalization exclusion avoids minimality

/-- **Alternative (d) produces the decorated handoff envelope** —
`lem:typeA-cubic-switch-absorption` with `lem:typeA-high-degree-handoff`: a
surviving first separator has ambient degree at least four and, with the two
separated connector tails as its arms, produces a decorated handoff fan
envelope whose counted core is the support itself, which is exit `(7)`.  The
high-degree conversion and the denial of the absorbing clause are the
branch's committed facts, taken as hypotheses and never restated. -/
theorem exists_envelope_of_traceSurvivingSeparator
    {object : FiniteObject.{u}} {support : Finset object.Vertex}
    {threshold : Nat} {LengthOK : Nat → Prop} {receiver load : object.Vertex}
    {basin : Finset object.Vertex} {HighDegree : object.Vertex → Prop}
    {Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop}
    (separated : TraceSurvivingSeparator object support threshold LengthOK
      receiver load basin)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (high : ∀ vertex : object.Vertex, 3 < object.degree vertex →
      HighDegree vertex)
    (denied : ∀ centre first second : object.Vertex,
      ¬ Absorbing centre first second) :
    ∃ envelope : DecoratedHandoff.Envelope object LengthOK HighDegree Absorbing,
      envelope.core = support ∧ envelope.decorations.Nonempty := by
  obtain ⟨family, _loadMember, leftLoad, rightLoad, leftMember, rightMember,
    _distinct, separation, _leftPath, _rightPath, reading, surviving⟩ :=
    separated
  have leftChain :
      (separation.nextLeft :: separation.tailLeft).IsChain object.graph.Adj := by
    have chain := separation.left.chain
    rw [separation.leftEq] at chain
    exact (List.isChain_cons.mp (List.isChain_append.mp chain).2.1).2
  have rightChain :
      (separation.nextRight :: separation.tailRight).IsChain object.graph.Adj := by
    have chain := separation.right.chain
    rw [separation.rightEq] at chain
    exact (List.isChain_cons.mp (List.isChain_append.mp chain).2.1).2
  have leftNodup :
      (separation.nextLeft :: separation.tailLeft).Nodup := by
    have nodup := separation.left.nodup
    rw [separation.leftEq] at nodup
    exact (List.nodup_cons.mp (List.nodup_append.mp nodup).2.1).2
  have rightNodup :
      (separation.nextRight :: separation.tailRight).Nodup := by
    have nodup := separation.right.nodup
    rw [separation.rightEq] at nodup
    exact (List.nodup_cons.mp (List.nodup_append.mp nodup).2.1).2
  have leftLast :
      (separation.nextLeft :: separation.tailLeft).getLast? =
        some separation.left.terminal := by
    have last := separation.left.terminal_last
    rw [separation.leftEq] at last
    simpa using last
  have rightLast :
      (separation.nextRight :: separation.tailRight).getLast? =
        some separation.right.terminal := by
    have last := separation.right.terminal_last
    rw [separation.rightEq] at last
    simpa using last
  have leftInterior : ∀ vertex ∈ separation.nextLeft :: separation.tailLeft,
      vertex ∈ support ∨ vertex = separation.separator →
        (separation.nextLeft :: separation.tailLeft).getLast? = some vertex := by
    intro vertex member alternatives
    rcases alternatives with inside | rfl
    · have memberTail : vertex ∈ separation.left.path.tail := by
        rw [separation.leftEq]
        simp only [List.tail_append_of_ne_nil separation.common_ne_nil]
        exact List.mem_append_right _ (by simp [member])
      exact leftLast.trans (congrArg some
        (separation.left.interior vertex memberTail inside).symm)
    · have nodup := separation.left.nodup
      rw [separation.leftEq] at nodup
      exact False.elim
        ((List.nodup_cons.mp (List.nodup_append.mp nodup).2.1).1 member)
  have rightInterior : ∀ vertex ∈ separation.nextRight :: separation.tailRight,
      vertex ∈ support ∨ vertex = separation.separator →
        (separation.nextRight :: separation.tailRight).getLast? = some vertex := by
    intro vertex member alternatives
    rcases alternatives with inside | rfl
    · have memberTail : vertex ∈ separation.right.path.tail := by
        rw [separation.rightEq]
        simp only [List.tail_append_of_ne_nil separation.common_ne_nil]
        exact List.mem_append_right _ (by simp [member])
      exact rightLast.trans (congrArg some
        (separation.right.interior vertex memberTail inside).symm)
    · have nodup := separation.right.nodup
      rw [separation.rightEq] at nodup
      exact False.elim
        ((List.nodup_cons.mp (List.nodup_append.mp nodup).2.1).1 member)
  let envelope := DecoratedHandoff.envelopeOfSeparation separation
    (separation.nextLeft :: separation.tailLeft)
    (separation.nextRight :: separation.tailRight) (by simp) (by simp)
    leftChain rightChain leftNodup rightNodup
    ⟨separation.left.terminal, leftLast, separation.left.terminal_inside⟩
    ⟨separation.right.terminal, rightLast, separation.right.terminal_inside⟩
    leftInterior rightInterior
    (high separation.separator
      (DecoratedHandoff.four_le_degree_of_surviving surviving))
    avoids (denied _ _ _) (denied _ _ _)
  exact ⟨envelope, rfl, by simp [envelope,
    DecoratedHandoff.envelopeOfSeparation]⟩

/-- **Alternative (d) is refuted where no decorated handoff is produced**: a
surviving separator would produce the envelope. -/
theorem not_traceSurvivingSeparator_of_noEnvelope {object : FiniteObject.{u}}
    {support : Finset object.Vertex} {threshold : Nat} {LengthOK : Nat → Prop}
    {receiver load : object.Vertex} {basin : Finset object.Vertex}
    {HighDegree : object.Vertex → Prop}
    {Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (high : ∀ vertex : object.Vertex, 3 < object.degree vertex →
      HighDegree vertex)
    (denied : ∀ centre first second : object.Vertex,
      ¬ Absorbing centre first second)
    (noEnvelope : ¬ ∃ envelope :
        DecoratedHandoff.Envelope object LengthOK HighDegree Absorbing,
      envelope.core = support ∧ envelope.decorations.Nonempty) :
    ¬ TraceSurvivingSeparator object support threshold LengthOK receiver load
      basin :=
  fun separated => noEnvelope
    (exists_envelope_of_traceSurvivingSeparator separated avoids high denied)

section SilentLane

attribute [local instance] vertexDecEq

/-- The silent excess consists of routed loads. -/
theorem silentExcess_subset_routedLoads (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) :
    VisibleEntry.silentExcess object support threshold scale receiver ⊆
      object.routedLoads support threshold receiver :=
  Finset.sdiff_subset.trans Finset.sdiff_subset

/-- **`lem:typeA-reduced-silent-residual`, per unpaid silent load**: either the
load carries an exit-(4) witness at the empty peeling — alternative (a) at its
selected basin — or its basin is target-complete-minimal and the load is a
route-8 entry.  Alternatives (b), (c), (d) are refuted by the supplied
standing invariants. -/
theorem exists_witness_or_route8Entry {object : FiniteObject.{u}}
    {support : Finset object.Vertex} {threshold scale : Nat}
    {LengthOK : Nat → Prop} {receiver load : object.Vertex}
    (connected : SupportComponents.Connected.ConnectedOn object support)
    (loadRouted : load ∈ object.routedLoads support threshold receiver)
    (noQuotient : ∀ basin : Finset object.Vertex,
      select? object support threshold receiver load = some basin →
      ¬ ∃ retained,
        TraceResponseQuotient object support threshold LengthOK receiver load
          basin retained)
    (exclusion : ∀ enlarged : Finset object.Vertex,
      ¬ Strategy.InterfaceReplacement.ReplacementSupport
          (MinimumDegreeAtLeast threshold) (HasCycleWithLength LengthOK) object
          enlarged)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold representative →
      HasCycleWithLength LengthOK representative)
    (noSeparator : ∀ basin : Finset object.Vertex,
      ¬ TraceSurvivingSeparator object support threshold LengthOK receiver load
        basin) :
    (∃ witness : ExitFour.Witness (HasCycleWithLength LengthOK) support
        threshold scale receiver ∅, witness.load = load) ∨
      Route8Entry object support threshold LengthOK receiver load := by
  classical
  obtain ⟨basin, selectedEq⟩ := exists_select?_eq_some_of_mem_routedLoads
    object support threshold connected loadRouted
  by_cases defect : TraceLocalTargetDefect object support threshold LengthOK
      receiver load basin
  · exact Or.inl
      (exists_witness_of_traceLocalTargetDefect selectedEq loadRouted defect)
  · exact Or.inr ⟨basin, selectedEq,
      targetCompleteMinimal_of_refutations (select?_traceComplete selectedEq)
        defect (noQuotient basin selectedEq) exclusion avoids minimality
        (noSeparator basin)⟩

/-- **`lem:typeA-reduced-silent-residual`, at the whole silent excess**: some
unpaid silent load carries an exit-(4) witness at the empty peeling, or every
unpaid silent load of the receiver is a route-8 entry. -/
theorem exists_witness_or_forall_route8Entry {object : FiniteObject.{u}}
    {support : Finset object.Vertex} {threshold scale : Nat}
    {LengthOK : Nat → Prop} {receiver : object.Vertex}
    (connected : SupportComponents.Connected.ConnectedOn object support)
    (noQuotient : ∀ load ∈
        VisibleEntry.silentExcess object support threshold scale receiver,
      ∀ basin : Finset object.Vertex,
      select? object support threshold receiver load = some basin →
      ¬ ∃ retained,
        TraceResponseQuotient object support threshold LengthOK receiver load
          basin retained)
    (exclusion : ∀ enlarged : Finset object.Vertex,
      ¬ Strategy.InterfaceReplacement.ReplacementSupport
          (MinimumDegreeAtLeast threshold) (HasCycleWithLength LengthOK) object
          enlarged)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold representative →
      HasCycleWithLength LengthOK representative)
    (noSeparator : ∀ load ∈
        VisibleEntry.silentExcess object support threshold scale receiver,
      ∀ basin : Finset object.Vertex,
      ¬ TraceSurvivingSeparator object support threshold LengthOK receiver load
        basin) :
    (∃ witness : ExitFour.Witness (HasCycleWithLength LengthOK) support
        threshold scale receiver ∅,
      witness.load ∈
        VisibleEntry.silentExcess object support threshold scale receiver) ∨
      ∀ load ∈ VisibleEntry.silentExcess object support threshold scale
          receiver,
        Route8Entry object support threshold LengthOK receiver load := by
  classical
  by_cases witnessed : ∃ load ∈
      VisibleEntry.silentExcess object support threshold scale receiver,
    ∃ witness : ExitFour.Witness (HasCycleWithLength LengthOK) support
        threshold scale receiver ∅, witness.load = load
  · obtain ⟨load, loadMember, witness, witnessLoad⟩ := witnessed
    exact Or.inl ⟨witness, witnessLoad ▸ loadMember⟩
  · refine Or.inr fun load loadMember => ?_
    rcases exists_witness_or_route8Entry connected
        (silentExcess_subset_routedLoads object support threshold scale receiver
          loadMember)
        (noQuotient load loadMember) exclusion avoids minimality
        (noSeparator load loadMember) with witness | entry
    · exact absurd ⟨load, loadMember, witness⟩ witnessed
    · exact entry

end SilentLane

end Hypostructure.Graph.Route8.TraceBasin
