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
and forgetting a coordinate with genuinely internal declared support — whose
reading is distinguished from the basin itself by an outside `∂B_u`-context
*of G*.  The only such context is G's own surroundings `G − B_u`
(`SupportAtom.outside G B_u`); the manuscript's "some outside context" ranged
over contexts that are not part of G.  At a target-avoiding G this is decided
false (`not_traceLocalTargetDefect`). -/
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
      ¬ (HasCycleWithLength LengthOK
          (glue (PresentedEntry.retainedReading object support basin threshold
              LengthOK (PresentedEntry.retainedBaseCoordinates object support
                retained))
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

/-- **`def:typeA-two-terminal-pressure-records`, stated about G** — the
canonical demand record at a selected basin: an *actual two-terminal record*, an
accepted event of the basin glued to its actual exterior `G − B_u`, with an
outside corridor between two distinct cut-boundary labels along event edges,
every interior vertex context-internal.  The manuscript's *profile record* (an
event glued to a distinguished non-actual context) is about a context that is
not part of G and has no G-form; it is removed. -/
def CanonicalDemandRecord (object : FiniteObject.{u})
    (basin : Finset object.Vertex) (LengthOK : Nat → Prop) : Prop :=
    ∃ certificate : CycleCertificate
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
                  ∃ inner, x = Sum.inr (Sum.inr inner)

/-- **Alternative (a) is decided false at a target-avoiding G**: G's retained
reading of `B_u` and G's own piece, both glued into `G − B_u`, carry no target
cycle, so they have the same target truth. -/
theorem not_traceLocalTargetDefect {object : FiniteObject.{u}}
    {support : Finset object.Vertex} {threshold : Nat} {LengthOK : Nat → Prop}
    {receiver load : object.Vertex} {basin : Finset object.Vertex}
    (avoids : ¬ HasCycleWithLength LengthOK object) :
    ¬ TraceLocalTargetDefect object support threshold LengthOK receiver load
      basin := by
  rintro ⟨retained, _retainedSubset, _nontrivial, defect⟩
  exact defect (iff_of_false
    (PresentedEntry.not_target_glue_retainedReading_outside avoids _)
    (Strategy.InterfaceReplacement.not_target_glue_piece_outside avoids basin))

/-- **`lem:typeA-pressure-records-canonical`, at G** — every target-defect entry
carries its canonical demand record.  At a target-avoiding G there is no
target-defect entry (`not_traceLocalTargetDefect`), so the implication holds
because its premise is decided false. -/
theorem exists_record_of_traceLocalTargetDefect
    {object : FiniteObject.{u}} {support : Finset object.Vertex}
    {threshold : Nat} {LengthOK : Nat → Prop}
    {receiver load : object.Vertex} {basin : Finset object.Vertex}
    (defect : TraceLocalTargetDefect object support threshold LengthOK
      receiver load basin)
    (avoids : ¬ HasCycleWithLength LengthOK object) :
    CanonicalDemandRecord object basin LengthOK :=
  absurd defect (not_traceLocalTargetDefect avoids)

/-- **Alternative (b) occurs at every trace basin of a routed load of G**
(Lean improvement, decided at G).  The response quotient forgetting every
declared coordinate is nontrivial — it forgets the trace incidence of the
nondegenerate trace `T_u ⊆ B_u` (`load ≠ receiver`) — and its G-form
completeness clause is decided true at a target-avoiding G
(`traceResponseQuotient_complete_of_avoids`). -/
theorem exists_traceResponseQuotient_of_avoids {object : FiniteObject.{u}}
    {support : Finset object.Vertex} {threshold : Nat} {LengthOK : Nat → Prop}
    {receiver load : object.Vertex} {basin : Finset object.Vertex}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (receiverMem : receiver ∈ object.receivers support threshold)
    (loadRouted : load ∈ object.routedLoads support threshold receiver)
    (complete : TraceComplete object support threshold receiver load basin) :
    ∃ retained, TraceResponseQuotient object support threshold LengthOK receiver
      load basin retained := by
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
  refine ⟨ResponseQuotient.forgetting ∅, Finset.empty_subset _, ?_,
    traceResponseQuotient_complete_of_avoids avoids _⟩
  refine ⟨PresentedEntry.TraceCoordinate.traceIncidence, ?_,
    Finset.notMem_empty _, Or.inl ⟨rfl, trace, traceSelected, tracePositive,
      traceInside⟩⟩
  change PresentedEntry.TraceCoordinate.traceIncidence ∈
    PresentedEntry.traceCoordinates object support threshold receiver load
  exact Finset.mem_insert_self _ _

/-- **No trace basin of a routed load of G is target-complete-minimal**
(Lean improvement, decided at G): alternative (b) always occurs
(`exists_traceResponseQuotient_of_avoids`). -/
theorem not_targetCompleteMinimal_of_avoids {object : FiniteObject.{u}}
    {support : Finset object.Vertex} {threshold : Nat} {LengthOK : Nat → Prop}
    {receiver load : object.Vertex} {basin : Finset object.Vertex}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (receiverMem : receiver ∈ object.receivers support threshold)
    (loadRouted : load ∈ object.routedLoads support threshold receiver) :
    ¬ TargetCompleteMinimal object support threshold LengthOK receiver load
      basin := fun minimal =>
  minimal.2.2.1
    (exists_traceResponseQuotient_of_avoids avoids receiverMem loadRouted
      minimal.1)

/-- **No routed load of G is a route-8 entry** (Lean improvement, decided at
G): its selected basin is never target-complete-minimal. -/
theorem not_route8Entry_of_avoids {object : FiniteObject.{u}}
    {support : Finset object.Vertex} {threshold : Nat} {LengthOK : Nat → Prop}
    {receiver load : object.Vertex}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (receiverMem : receiver ∈ object.receivers support threshold)
    (loadRouted : load ∈ object.routedLoads support threshold receiver) :
    ¬ Route8Entry object support threshold LengthOK receiver load := by
  rintro ⟨_basin, _selected, minimal⟩
  exact not_targetCompleteMinimal_of_avoids avoids receiverMem loadRouted
    minimal

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
