import Hypostructure.Graph.TypeAVisibleResponseCoordinate

/-!
# Canonical traces carried by selected visible response coordinates

The visible-four package already proves that each selected return is visible for
its originating load.  This file exposes the canonical trace and the two exact
visibility alternatives from that proof.  No trace or ownership witness is
supplied by a caller.
-/

namespace Hypostructure.Graph.ExitFour.VisibleFourUnpeeledPackage

open Hypostructure

universe u

variable {object : FiniteObject.{u}}
variable {support : Finset object.Vertex} {threshold scale : Nat}
variable {receiver : object.Vertex} {peeled : Finset object.Vertex}

/-- The canonical trace carried by a selected visible response coordinate. -/
noncomputable def selectedTrace
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :
    object.graph.Path load.1 receiver :=
  Classical.choose (package.selectedReturn_visible load.1 load.2)

/-- The exposed trace is exactly the trace selected by the ambient canonical
trace schedule. -/
theorem selectedTrace_selected
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :
    object.tracePath? support threshold load.1 receiver =
      some (package.selectedTrace load) :=
  (Classical.choose_spec
    (package.selectedReturn_visible load.1 load.2)).1

/-- The selected return carries its exposed canonical trace by exactly one of
the two visibility clauses of `VisibleEntry.VisibleFor`. -/
theorem selectedTrace_carried
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :
    (package.selectedTrace load).1.support.IsSuffix
        (package.selectedReturn load.1 load.2).channel.support ∨
      ∃ terminalEdge : Sym2 object.Vertex,
        (package.selectedTrace load).1.edges.getLast? = some terminalEdge ∧
          VisibleEntry.canonicalChannel? object support
              (package.selectedReturn load.1 load.2).entry receiver terminalEdge
                (package.selectedTrace load) =
            some ⟨(package.selectedReturn load.1 load.2).channel,
              (package.selectedReturn load.1 load.2).isChannel.1⟩ :=
  (Classical.choose_spec
    (package.selectedReturn_visible load.1 load.2)).2

/-- Every selected response channel literally contains its originating
canonical trace.  The second visibility clause reaches the same conclusion
through the trace-owning `canonicalChannel?` selection; it is not inferred from
the unrelated source orders of the trace and channel schedules. -/
theorem selectedTrace_isSuffix
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :
    (package.selectedTrace load).1.support.IsSuffix
      (package.selectedReturn load.1 load.2).channel.support := by
  rcases package.selectedTrace_carried load with carried | canonical
  · exact carried
  · obtain ⟨_terminalEdge, _traceLast, selected⟩ := canonical
    exact VisibleEntry.traceSuffix_of_canonicalChannel?_eq_some object selected

/-- Distinct selected loads carry distinct canonical trace vertex lists.  This
is the paper's "distinct canonical traces" assertion, derived from their
distinct initial vertices rather than stored as an extra package field. -/
theorem selectedTrace_support_ne_of_ne
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    {left right : package.SelectedLoad} (different : left ≠ right) :
    (package.selectedTrace left).1.support ≠
      (package.selectedTrace right).1.support := by
  intro equal
  apply different
  apply Subtype.ext
  have heads := congrArg List.head? equal
  have leftHead : (package.selectedTrace left).1.support.head? = some left.1 := by
    rw [List.head?_eq_some_head
      (package.selectedTrace left).1.support_ne_nil,
      (package.selectedTrace left).1.head_support]
  have rightHead : (package.selectedTrace right).1.support.head? = some right.1 := by
    rw [List.head?_eq_some_head
      (package.selectedTrace right).1.support_ne_nil,
      (package.selectedTrace right).1.head_support]
  rw [leftHead, rightHead] at heads
  exact Option.some.inj heads

end Hypostructure.Graph.ExitFour.VisibleFourUnpeeledPackage
