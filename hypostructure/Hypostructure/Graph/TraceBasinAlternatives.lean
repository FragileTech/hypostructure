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
  context of G (only `G − B_u`) — decided false at a target-avoiding G;
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

/-- **Alternative (a) of `def:typeA-trace-basin`, stated about G.**  A
trace-local quotient of `ρ_u(B_u)` — retaining a subset of the declared family
and forgetting a coordinate with genuinely internal declared support — is
distinguished by an outside `∂B_u`-context: some realization of the quotient,
glued into the context, has a different target truth from `ρ_u(B_u)`.  Stated
about G, the context is G's own surroundings `G − B_u`
(`SupportAtom.outside G B_u`) and the realizations are the pieces constructed
from G at `B_u` (`GConstructedPiece`) that carry every retained coordinate
exactly (`QuotientRealization`).  A reading of G glued into `G − B_u` is a
subgraph of G and never separates; a fold of two interior basin vertices with no
common neighbour does, at a minimal G (`traceLocalTargetDefect_of_foldPair`). -/
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
      ∃ realization : GConstructedPiece object basin,
        QuotientRealization object support basin threshold receiver load
            (ResponseQuotient.forgetting retained) realization.toPiece ∧
          ¬ (HasCycleWithLength LengthOK
              (glue realization.toPiece
                (Strategy.InterfaceReplacement.SupportAtom.outside object basin)) ↔
            HasCycleWithLength LengthOK
              (glue (Strategy.InterfaceReplacement.SupportAtom.piece object basin)
                (Strategy.InterfaceReplacement.SupportAtom.outside object basin)))

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
`S_z` — the switch constructed from G at the separation
(`Separation.switched`) — is neither target-defective, nor target-complete,
nor valid only after enlarging: `z` is surviving.  At a target-avoiding G this
is: the switched graph has no accepted cycle and `z` has an unused ambient
incidence (`DecoratedHandoff.Surviving.of_avoids`). -/
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
                  DecoratedHandoff.Surviving (HasCycleWithLength LengthOK)
                    separation
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
  exact delocalization.false_of_minimal minimality

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
  obtain ⟨retained, retainedSubset, nontrivial, realization, realizes,
    targetDefect⟩ := defect
  refine ⟨⟨load, ?_, .q3
    { LengthOK := LengthOK
      target_eq := rfl
      basin := basin
      selected := selected
      retained := retained
      retained_subset := retainedSubset
      nontrivial := nontrivial
      realization := realization
      realizes := realizes
      targetDefect := targetDefect }⟩, rfl⟩
  rw [ExitFour.mem_unpeeledLoads]
  exact ⟨loadRouted, Finset.notMem_empty load⟩

/-- **`def:typeA-two-terminal-pressure-records`, stated about G** — the
canonical demand record at a selected basin.  At G every distinguishing token
is read in the actual exterior `G − B_u`; its realization is a piece
constructed from G at `B_u`, in G's boundary-degree fibre and separated from G's
own piece there, and its event is an accepted cycle of that realization glued
into `G − B_u`.  The record is

* the **actual two-terminal record**: an outside corridor along event edges
  between two distinct cut-boundary labels, every interior vertex
  context-internal; or
* the **internal event**: the event is a cycle of the realization itself; or
* the **exterior event**: the event avoids the realization's interior
  vertices.

The last two are the cases the manuscript excludes through
`lem:typeA-internal-quotient-mixed` ("if the event were contained entirely in
`X`, it would be a power-of-two cycle in the target-safe support"); a
realization built from G is not a subgraph of G, so at G they are explicit
alternatives rather than impossibilities. -/
def CanonicalDemandRecord (object : FiniteObject.{u})
    (basin : Finset object.Vertex) (LengthOK : Nat → Prop) : Prop :=
  ∃ realization : GConstructedPiece object basin,
    realization.Separated (HasCycleWithLength LengthOK) GConstructedPiece.own ∧
    ∃ certificate : CycleCertificate
        (glue realization.toPiece
          (Strategy.InterfaceReplacement.SupportAtom.outside object basin))
        LengthOK,
      (∃ left right : (Strategy.InterfaceReplacement.SupportAtom.boundary
          object basin).Vertex,
        left ≠ right ∧
          ∃ corridor : (glueGraph realization.toPiece
              (Strategy.InterfaceReplacement.SupportAtom.outside object
                basin)).Walk (.inl left) (.inl right),
            corridor.edges ⊆ certificate.walk.edges ∧
              ∀ x ∈ corridor.support,
                x = Sum.inl left ∨ x = Sum.inl right ∨
                  ∃ inner, x = Sum.inr (Sum.inr inner)) ∨
      (∃ (pieceBase : (Strategy.InterfaceReplacement.SupportAtom.boundary object
            basin).Vertex ⊕ realization.toPiece.Internal)
          (lifted : realization.toPiece.graph.Walk pieceBase pieceBase),
        lifted.IsCycle ∧ lifted.length = certificate.walk.length) ∨
      (∀ inner : realization.toPiece.Internal,
        (Sum.inr (Sum.inl inner) : GluedVertex realization.toPiece
          (Strategy.InterfaceReplacement.SupportAtom.outside object basin)) ∉
            certificate.walk.support)

/-- **`lem:typeA-pressure-records-canonical`, at G** — every target-defect entry
carries its canonical demand record.  The defect's realization carries an
accepted cycle in `G − B_u` (G's own piece does not); split that event by
`GluedCycleSides`: two distinct labels around a context-internal vertex give
the outside corridor; a context-free event lifts to the realization or crosses
a context-owned label edge (a one-edge corridor); a context event with fewer
than two labels meets no interior vertex of the realization. -/
theorem exists_record_of_traceLocalTargetDefect
    {object : FiniteObject.{u}} {support : Finset object.Vertex}
    {threshold : Nat} {LengthOK : Nat → Prop}
    {receiver load : object.Vertex} {basin : Finset object.Vertex}
    (defect : TraceLocalTargetDefect object support threshold LengthOK
      receiver load basin)
    (avoids : ¬ HasCycleWithLength LengthOK object) :
    CanonicalDemandRecord object basin LengthOK := by
  classical
  obtain ⟨_retained, _subset, _nontrivial, realization, realizes, defect⟩ := defect
  have pieceFree := Strategy.InterfaceReplacement.not_target_glue_piece_outside
    avoids basin
  have accepted : HasCycleWithLength LengthOK (glue realization.toPiece
      (Strategy.InterfaceReplacement.SupportAtom.outside object basin)) := by
    by_contra free
    exact defect (iff_of_false free pieceFree)
  have separated : realization.Separated (HasCycleWithLength LengthOK)
      GConstructedPiece.own :=
    ⟨realizes.1, fun same => pieceFree (same.mp accepted)⟩
  obtain ⟨certificate⟩ := accepted
  refine ⟨realization, separated, certificate, ?_⟩
  by_cases twoLabels : ∃ left right : (Strategy.InterfaceReplacement.SupportAtom.boundary
      object basin).Vertex, left ≠ right ∧
      (Sum.inl left : GluedVertex realization.toPiece
        (Strategy.InterfaceReplacement.SupportAtom.outside object basin)) ∈
          certificate.walk.support ∧
      (Sum.inl right : GluedVertex realization.toPiece
        (Strategy.InterfaceReplacement.SupportAtom.outside object basin)) ∈
          certificate.walk.support
  · by_cases contextMeet : ∃ inner, (Sum.inr (Sum.inr inner) : GluedVertex
        realization.toPiece
        (Strategy.InterfaceReplacement.SupportAtom.outside object basin)) ∈
          certificate.walk.support
    · obtain ⟨inner, innerMem⟩ := contextMeet
      obtain ⟨left, right, distinct, leftMem, rightMem⟩ := twoLabels
      exact Or.inl (GluedCycleSides.exists_corridor_of_cycle_contextInternal
        certificate.isCycle innerMem distinct leftMem rightMem)
    · push_neg at contextMeet
      rcases GluedCycleSides.cycle_pieceLift_or_contextInternal_or_labelDart
          certificate.isCycle with lifted | ⟨inner, innerMem⟩ |
          ⟨dartLeft, dartRight, dartDistinct, _leftMem, _rightMem, dartAdj,
            dartEdge⟩
      · exact Or.inr (Or.inl lifted)
      · exact absurd innerMem (contextMeet inner)
      · have dartGlueAdj : (glueGraph realization.toPiece
            (Strategy.InterfaceReplacement.SupportAtom.outside object
              basin)).Adj (.inl dartLeft) (.inl dartRight) := by
          refine (glueGraph_adj_iff _ _ _ _).mpr (Or.inr ⟨.inl dartLeft,
            .inl dartRight, dartAdj, ?_, ?_⟩) <;> rfl
        refine Or.inl ⟨dartLeft, dartRight, dartDistinct,
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
  · by_cases contextMeet : ∃ inner, (Sum.inr (Sum.inr inner) : GluedVertex
        realization.toPiece
        (Strategy.InterfaceReplacement.SupportAtom.outside object basin)) ∈
          certificate.walk.support
    · refine Or.inr (Or.inr ?_)
      intro pieceInner pieceMem
      obtain ⟨inner, innerMem⟩ := contextMeet
      exact twoLabels (GluedCycleSides.exists_two_labels_of_cycle_sides
        certificate.isCycle pieceMem innerMem)
    · push_neg at contextMeet
      rcases GluedCycleSides.cycle_pieceLift_or_contextInternal_or_labelDart
          certificate.isCycle with lifted | ⟨inner, innerMem⟩ |
          ⟨dartLeft, dartRight, dartDistinct, leftMem, rightMem, _dartAdj,
            _dartEdge⟩
      · exact Or.inr (Or.inl lifted)
      · exact absurd innerMem (contextMeet inner)
      · exact absurd ⟨dartLeft, dartRight, dartDistinct, leftMem, rightMem⟩
          twoLabels

/-- **A fold pair of the selected basin is a trace-local target defect**
(alternative (a), at a minimal G).  Two interior vertices of `B_u` with no
common neighbour in G fold to a piece constructed from G that carries every
declared coordinate avoiding them; forgetting in addition the trace incidence of
the nondegenerate trace `T_u ⊆ B_u` (`load ≠ receiver`) makes the quotient
nontrivial, and the fold glued into `G − B_u` carries a target cycle
(`GConstructedPiece.response_fold_of_minimal`) while G's piece does not. -/
theorem traceLocalTargetDefect_of_foldPair {object : FiniteObject.{u}}
    {support : Finset object.Vertex} {threshold : Nat} {LengthOK : Nat → Prop}
    {receiver load : object.Vertex} {basin : Finset object.Vertex}
    (two : 2 ≤ threshold) (baseline : MinimumDegreeAtLeast threshold object)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold H → HasCycleWithLength LengthOK H)
    (receiverMem : receiver ∈ object.receivers support threshold)
    (loadRouted : load ∈ object.routedLoads support threshold receiver)
    (complete : TraceComplete object support threshold receiver load basin)
    (keep remove :
      Strategy.InterfaceReplacement.SupportAtom.PieceInternal object basin)
    (different : keep ≠ remove)
    (noCommon : ∀ common, ¬ object.IsCommonNeighbor keep.1 remove.1 common) :
    TraceLocalTargetDefect object support threshold LengthOK receiver load
      basin := by
  classical
  have loadDegree : object.internalDegree support load = threshold :=
    (object.mem_routedLoads.mp loadRouted).2.1
  have receiverDegree : object.internalDegree support receiver < threshold :=
    (object.mem_receivers.mp receiverMem).2
  have loadNeReceiver : load ≠ receiver := by
    intro same
    subst load
    omega
  obtain ⟨trace, traceSelected, traceInside⟩ := complete.2.1
  have tracePositive : 0 < trace.1.length := by
    apply Nat.pos_of_ne_zero
    intro zero
    exact loadNeReceiver (trace.1.eq_of_length_eq_zero zero)
  let retained := ((PresentedEntry.traceCoordinates object support threshold
      receiver load).filter fun coordinate =>
        keep.1 ∉ PresentedEntry.traceDeclaredSupport object support threshold
            receiver load coordinate ∧
          remove.1 ∉ PresentedEntry.traceDeclaredSupport object support threshold
            receiver load coordinate).erase
    PresentedEntry.TraceCoordinate.traceIncidence
  refine ⟨retained, ?_, ?_, GConstructedPiece.fold keep remove different noCommon,
    ?_, ?_⟩
  · intro coordinate member
    exact (Finset.mem_filter.mp (Finset.mem_erase.mp member).2).1
  · refine ⟨PresentedEntry.TraceCoordinate.traceIncidence, ?_,
      Finset.notMem_erase _ _, Or.inl ⟨rfl, trace, traceSelected, tracePositive,
        traceInside⟩⟩
    change PresentedEntry.TraceCoordinate.traceIncidence ∈
      PresentedEntry.traceCoordinates object support threshold receiver load
    exact Finset.mem_insert_self _ _
  · refine quotientRealization_fold object support basin threshold receiver load
      retained keep remove different noCommon ?_
    intro coordinate member
    exact (Finset.mem_filter.mp (Finset.mem_erase.mp member).2).2
  · intro same
    exact Strategy.InterfaceReplacement.not_target_glue_piece_outside avoids basin
      (same.mp (GConstructedPiece.response_fold_of_minimal two baseline minimal
        keep remove different noCommon))

/-- **Where alternative (a) is absent, the basin interior is pairwise
common-neighboured** (at a minimal G): every two distinct interior vertices of
the selected basin have a common neighbour in G.  Otherwise they fold
(`traceLocalTargetDefect_of_foldPair`). -/
theorem exists_commonNeighbor_of_not_traceLocalTargetDefect
    {object : FiniteObject.{u}}
    {support : Finset object.Vertex} {threshold : Nat} {LengthOK : Nat → Prop}
    {receiver load : object.Vertex} {basin : Finset object.Vertex}
    (two : 2 ≤ threshold) (baseline : MinimumDegreeAtLeast threshold object)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold H → HasCycleWithLength LengthOK H)
    (receiverMem : receiver ∈ object.receivers support threshold)
    (loadRouted : load ∈ object.routedLoads support threshold receiver)
    (complete : TraceComplete object support threshold receiver load basin)
    (noDefect : ¬ TraceLocalTargetDefect object support threshold LengthOK
      receiver load basin)
    (keep remove :
      Strategy.InterfaceReplacement.SupportAtom.PieceInternal object basin)
    (different : keep ≠ remove) :
    ∃ common, object.IsCommonNeighbor keep.1 remove.1 common := by
  by_contra none
  push_neg at none
  exact noDefect (traceLocalTargetDefect_of_foldPair two baseline avoids minimal
    receiverMem loadRouted complete keep remove different none)

/-- **Target-complete-minimality from the branch's refutations**: the selected
basin is trace-complete, and each of the four failure alternatives is refuted
— (a), (b), and (d) by hypothesis, and (c) through
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
    _distinct, separation, _leftPath, _rightPath, surviving⟩ :=
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
