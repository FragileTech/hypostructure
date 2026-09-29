import Hypostructure.Graph.Contracts.RouteEight.EntryCensus
import Hypostructure.Graph.Contracts.RouteEight.Terminal

/-!
# Contracts: route 8 read on the pieces constructed from G (idx 8700)

The realizations of a route-`8` entry's declared trace-response state are the
pieces constructed from G at its selected basin (`Graph.GConstructedPiece`),
read in G's own surroundings.  A fold of two interior basin vertices with no
common neighbour is an exit-`(4)` peel (Q3), a nonempty essential core means
the declared family determines the target, every complete carrier set holds
every fold pair, and a two-support entry with a nonempty core is an exit-`(4)`
peel (Q5).
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

attribute [local instance] Graph.Route8.vertexDecEq

/-- **Route 8 read on the pieces constructed from G** (idx 8700): at every
unified entry, a fold pair of the selected basin is an exit-(4) peel of the load
(alternative (a), type Q3), a nonempty core determines the target, every
complete carrier set holds every fold pair, and a two-support entry with a
nonempty core is an exit-(4) peel (Q5, `thm:typeA-two-carrier-nogo` run at G). -/
theorem route8FoldPeels (data : Parameters) (object : FiniteObject.{u})
    (two : 2 ≤ data.threshold)
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold representative →
      Graph.HasCycleWithLength data.LengthOK representative) :
    Route8FoldPeelsStatement data object := by
  classical
  intro index indexMem
  obtain ⟨component, componentMem, pieceEq, receiverMem, loadMem⟩ :=
    mem_entriesOfComponents.mp indexMem
  have connected : Graph.SupportComponents.Connected.ConnectedOn object
      index.1 := by
    rw [pieceEq]
    exact Graph.SupportComponents.Connected.connectedOn_of_mem_order object _
      ((Graph.FiniteObject.mem_canonicalPieces _ _).1
        (Finset.mem_filter.mp componentMem).1)
  have receiverAt : index.2.1 ∈ object.receivers index.1 data.threshold :=
    (Finset.mem_filter.mp receiverMem).1
  have loadRouted : index.2.2 ∈ object.routedLoads index.1 data.threshold
      index.2.1 :=
    (Finset.mem_sdiff.mp loadMem).1
  obtain ⟨basin₀, selectedEq⟩ :=
    Graph.Route8.TraceBasin.exists_select?_eq_some_of_mem_routedLoads
      object index.1 data.threshold connected loadRouted
  have selectedCensus : Graph.Route8.TraceBasin.select? object index.1
      data.threshold index.2.1 index.2.2 =
        some (Graph.Route8Census.basin object data.threshold index) := by
    rw [Graph.Route8Census.basin, selectedEq]
    rfl
  have complete := Graph.Route8.TraceBasin.select?_traceComplete selectedCensus
  refine ⟨fun keep remove different noCommon => ?_, fun one => ?_,
    fun D completeD keep remove different noCommon => ?_,
    fun twoCarrier one => ?_⟩
  · have defect := Graph.Route8.TraceBasin.traceLocalTargetDefect_of_foldPair two
      baseline avoids minimality receiverAt loadRouted complete keep remove
      different noCommon
    exact ⟨defect, Graph.Route8.TraceBasin.exists_witness_of_traceLocalTargetDefect
      selectedCensus loadRouted defect⟩
  · exact Graph.Route8.Entry.determined_of_one_le_alpha _ one
  · exact Graph.Route8.PresentedEntry.ofTraceBasin_foldPair_held_of_complete two
      baseline avoids minimality completeD keep remove different noCommon
  · obtain ⟨canonical, negative⟩ := route8UnifiedComponents_canonical data object
    exact twoCarrier_exitFour_of_core data.LengthOK object
      (canonicalWindowPacking data object) (route8UnifiedComponents data object)
      data.threshold data.dischargeScale canonical negative indexMem twoCarrier
      selectedCensus one

end Hypostructure.Graph.Contracts.RouteEight
