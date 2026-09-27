/-
fix2-348: the exact obstruction to Visibility(R) at G (tex 15362).
Scratch evidence, not part of the build.  Compile from `hypostructure/` with
`lake env lean <this file>`.

At an entry ξ of G's unified set whose essential core has α(ξ) ≤ 1:
* (b) HOLDS at ξ (`b_of_alpha_le_one`, via the project's own
  `route8Entry_smallCoreQuotient`, i.e. `lem:typeA-one-terminal-collapse`);
* the declared u-supported algebra is identically FALSE, at every piece and
  every context (`declaredAlgebra_empty_of_alpha_le_one`);
* so Visibility(R) ⟺ ¬ Target(R ⊕ Y_G), and for every fold R of B_u
  minimality refutes it (`not_visibility_of_alpha_le_one`);
* hence G's [348] residual arm is FORCED by any such entry
  (`residual_of_alpha_le_one`): closing [348] is at least as strong as
  α(ξ) ≥ 2 at every unified entry, which is the conclusion of
  `lem:typeA-unified-carriers` itself; on G's ledger that bound is
  K .route8UnifiedEntryCensus (340), derived AFTER [348], on its free arm,
  from quotient-freeness (`route8EntryFacts.alphaBound`).
-/
import Hypostructure.Graph.Contracts.RouteEight.EntryCensus

open Hypostructure Hypostructure.Graph Hypostructure.Graph.Strategy.Spine

universe u

namespace F1Obstruction348

attribute [local instance] Graph.Route8.vertexDecEq

/-- The declared algebra is empty at an entry with `α ≤ 1`: a visible declared
event is a core-retained crossing coordinate, which has two carriers
(`lem:typeA-carrier-cut-parity`), forcing `α ≥ 2`. -/
theorem declaredAlgebra_empty_of_alpha_le_one
    {object : FiniteObject.{u}} {support basin : Finset object.Vertex}
    {threshold : Nat} {LengthOK : Nat → Prop} {receiver load : object.Vertex}
    (small : ((Route8.PresentedEntry.ofTraceBasin object support basin threshold
      LengthOK receiver load).toEntry (HasCycleWithLength LengthOK)).alpha ≤ 1)
    (piece : BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin))
    (outside : OutsideContext
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin)) :
    ¬ Route8.TraceBasin.declaredAlgebra object support basin threshold LengthOK
        receiver load piece outside := by
  intro holds
  obtain ⟨coordinate, coreRetained, crossing⟩ :=
    Route8.TraceBasin.distinguishingEventCrosses holds
  have alphaTwo :=
    Route8.Entry.two_le_alpha_of_two_le_card_car _ coreRetained
      ((Route8.PresentedEntry.ofTraceBasin object support basin threshold
        LengthOK receiver load).two_le_card_car crossing)
  omega

/-- `Visibility(R)` of step 2b (verbatim). -/
def Visibility {object : FiniteObject.{u}} (support basin : Finset object.Vertex)
    (threshold : Nat) (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (R : BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin)) : Prop :=
  let atom := Strategy.InterfaceReplacement.SupportAtom.properAtom object basin
    connected proper
  HasCycleWithLength LengthOK (glue R atom.decomposition.outside) →
    Route8.TraceBasin.declaredAlgebra object support basin threshold LengthOK
      receiver load R atom.decomposition.outside

/-- **Visibility fails at G** at an `α ≤ 1` entry, for every fold of `B_u`:
minimality puts an accepted cycle in `R ⊕ Y_G`, and no declared coordinate can
see it. -/
theorem not_visibility_of_alpha_le_one
    {object : FiniteObject.{u}} {support basin : Finset object.Vertex}
    {threshold : Nat} (two : 2 ≤ threshold) {LengthOK : Nat → Prop}
    {receiver load : object.Vertex}
    (baseline : MinimumDegreeAtLeast threshold object)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold representative →
      HasCycleWithLength LengthOK representative)
    (small : ((Route8.PresentedEntry.ofTraceBasin object support basin threshold
      LengthOK receiver load).toEntry (HasCycleWithLength LengthOK)).alpha ≤ 1)
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (keep remove :
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal)
    (different : keep ≠ remove)
    (noCommon : ∀ x,
      ¬ ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
            (.inr keep) x ∧
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
          (.inr remove) x)) :
    ¬ Visibility support basin threshold LengthOK receiver load connected proper
      ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).identifyInternal
        keep remove different) := by
  intro visible
  obtain ⟨dBaseline, dSmaller⟩ :=
    Route8.PresentedEntry.foldRealization_baseline_and_smaller object basin
      threshold two connected proper keep remove different baseline noCommon
  exact declaredAlgebra_empty_of_alpha_le_one small _ _
    (visible (minimality _ dSmaller dBaseline))

/-- **(b) holds at an `α ≤ 1` unified entry of G** (the project's own
`lem:typeA-one-terminal-collapse` construction, empty crossing family). -/
theorem b_of_alpha_le_one (data : Parameters) (object : FiniteObject.{u})
    {index : Route8Census.Index object}
    (member : index ∈ route8UnifiedEntries data object)
    (small : ((Route8Census.presented object data.threshold data.LengthOK
      index).toEntry (HasCycleWithLength data.LengthOK)).alpha ≤ 1) :
    Route8.TraceBasin.select? object index.1 data.threshold index.2.1 index.2.2 =
        some (Route8Census.basin object data.threshold index) ∧
      ∃ retained, Route8.TraceBasin.TraceResponseQuotient object index.1
        data.threshold data.LengthOK index.2.1 index.2.2
        (Route8Census.basin object data.threshold index) retained := by
  classical
  obtain ⟨component, componentMem, pieceEq, receiverMem, loadMem⟩ :=
    Contracts.RouteEight.mem_entriesOfComponents.mp member
  have connected : SupportComponents.Connected.ConnectedOn object index.1 := by
    rw [pieceEq]
    exact SupportComponents.Connected.connectedOn_of_mem_order object _
      ((FiniteObject.mem_canonicalPieces _ _).1
        (Finset.mem_filter.mp componentMem).1)
  have loadRouted := (Finset.mem_sdiff.mp loadMem).1
  obtain ⟨basin₀, selectedEq⟩ :=
    Route8.TraceBasin.exists_select?_eq_some_of_mem_routedLoads
      object index.1 data.threshold connected loadRouted
  have selectedCensus : Route8.TraceBasin.select? object index.1 data.threshold
      index.2.1 index.2.2 =
        some (Route8Census.basin object data.threshold index) := by
    rw [Route8Census.basin, selectedEq]
    rfl
  refine ⟨selectedCensus, ?_⟩
  exact Contracts.RouteEight.route8Entry_smallCoreQuotient data object index.1
    index.2.1 index.2.2 (Finset.mem_filter.mp receiverMem).1 loadRouted
    (Route8.TraceBasin.select?_traceComplete selectedCensus)
    (crossing := ∅) (fun _ absurdMem => absurd absurdMem (Finset.notMem_empty _))
    small

/-- **The [348] residual is forced at G by any unified entry with `α ≤ 1`.** -/
theorem residual_of_alpha_le_one (data : Parameters) (object : FiniteObject.{u})
    {index : Route8Census.Index object}
    (member : index ∈ route8UnifiedEntries data object)
    (small : ((Route8Census.presented object data.threshold data.LengthOK
      index).toEntry (HasCycleWithLength data.LengthOK)).alpha ≤ 1) :
    ¬ Route8QuotientFreeStatement data object := by
  classical
  intro free
  obtain ⟨selectedCensus, quotient⟩ := b_of_alpha_le_one data object member small
  have free' : ∀ index ∈ route8UnifiedEntries data object,
      ∀ basin : Finset object.Vertex,
        Route8.TraceBasin.select? object index.1 data.threshold
            index.2.1 index.2.2 = some basin →
          ¬ ∃ retained,
            Route8.TraceBasin.TraceResponseQuotient object index.1
              data.threshold data.LengthOK index.2.1 index.2.2 basin retained := by
    delta Route8QuotientFreeStatement at free
    exact free
  exact free' index member _ selectedCensus quotient

end F1Obstruction348

#print axioms F1Obstruction348.declaredAlgebra_empty_of_alpha_le_one
#print axioms F1Obstruction348.not_visibility_of_alpha_le_one
#print axioms F1Obstruction348.b_of_alpha_le_one
#print axioms F1Obstruction348.residual_of_alpha_le_one
