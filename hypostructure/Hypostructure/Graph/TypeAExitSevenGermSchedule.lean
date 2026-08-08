import Hypostructure.Graph.TypeAVisibleResponseCoordinate
import Hypostructure.Graph.DecoratedHandoffEnvelope

/-!
# Finite connector-germ schedule before exit `(7)` realization

This is the maximal graph-derived prefix of the exit-`(7)` construction that
does not require a semantic `BoundaryPiece` realization.  Canonically selected
visible response coordinates retain their actual scheduled receiver-entry
returns.  A return whose outside connector does not revisit the receiver gives
the manuscript's simple rooted germ `w,h,...,x_g`.  The finite selected-load
order therefore gives an exact finite germ schedule, and its ordered square
gives the exact distinct-germ-pair schedule.

For every pair, the first separating vertex is selected by filtering the
ambient canonical vertex order with `DecoratedHandoff.SeparatesAt` and taking
its head.  The resulting record contains only the structural decomposition;
it deliberately is not a `DecoratedHandoff.Separation`, whose registered
boundary readings require the still-missing response-realization theorem.
-/

namespace Hypostructure.Graph

open Hypostructure
open Hypostructure.Core.Finite
open Hypostructure.Graph.DecoratedHandoff

universe u

variable {object : FiniteObject.{u}}

noncomputable section

local instance objectVertexDecidableEq : DecidableEq object.Vertex :=
  object.vertices.decEq

namespace VisibleEntry.ReceiverEntryReturn

variable {support : Finset object.Vertex} {receiver outside : object.Vertex}

/-- Exactly the extra condition needed for `w :: connector.support` to be a
simple rooted germ: the outside connector does not already contain its final
receiver. -/
def Rootable
    (return' : VisibleEntry.ReceiverEntryReturn object support receiver outside) :
    Prop :=
  receiver ∉ return'.connector.support

/-- A rootable canonical receiver-entry return gives the literal connector
germ `w,h,...,x_g`. -/
noncomputable def toRootedGerm
    (return' : VisibleEntry.ReceiverEntryReturn object support receiver outside)
    (port : outside ∈ VisibleEntry.completionPorts object support receiver)
    (rootable : return'.Rootable) :
    RootedGerm object support receiver outside := by
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have portAdj : object.graph.Adj receiver outside :=
    (VisibleEntry.mem_completionPorts.mp port).1
  have connectorPath : return'.connector.IsPath :=
    return'.isPath.of_append_left
  have connectorHead : return'.connector.support.head? = some outside := by
    rw [List.head?_eq_some_head return'.connector.support_ne_nil,
      return'.connector.head_support]
  refine
    { path := receiver :: return'.connector.support
      chain := ?_
      nodup := ?_
      rooted := by simp
      issued := by simpa using connectorHead
      terminal := return'.entry
      terminal_last := ?_
      terminal_inside := return'.isChannel.2 return'.entry
        return'.channel.start_mem_support
      interior := ?_ }
  · exact return'.connector.isChain_adj_cons_support portAdj
  · exact List.nodup_cons.mpr ⟨rootable, connectorPath.support_nodup⟩
  · rw [List.getLast?_eq_getLast_of_ne_nil (by simp)]
    simpa using return'.connector.getLast_support
  · intro vertex member inside
    simp only [List.tail_cons] at member
    by_contra different
    exact return'.connectorOutside vertex member different inside

end VisibleEntry.ReceiverEntryReturn

namespace ExitFour.VisibleFourUnpeeledPackage

variable {support : Finset object.Vertex} {threshold scale : Nat}
variable {receiver : object.Vertex} {peeled : Finset object.Vertex}
variable (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)

/-- A canonically selected response coordinate whose retained connector is an
actual simple rooted germ. -/
abbrev SelectedGerm :=
  {load : package.SelectedLoad //
    (package.selectedReturn load.1 load.2).Rootable}

/-- The actual rooted germ retained by one selected response coordinate. -/
noncomputable def SelectedGerm.germ (selected : package.SelectedGerm) :
    RootedGerm object support receiver package.outside :=
  (package.selectedReturn selected.1.1 selected.1.2).toRootedGerm package.port
    selected.2

/-- The finite selected-germ schedule in the canonical selected-load order. -/
noncomputable def germSchedule : Enumeration package.SelectedGerm := by
  classical
  let candidates : List package.SelectedGerm :=
    (selectedVisibleUnpeeledLoads support threshold scale receiver package.outside
      peeled).attach.filterMap fun load =>
        if rootable : (package.selectedReturn load.1 load.2).Rootable then
          some (⟨load, rootable⟩ : package.SelectedGerm)
        else none
  exact Enumeration.ofNodupList candidates.toFinset.toList
    (Finset.nodup_toList candidates.toFinset)

/-- Completeness of the finite germ schedule. -/
theorem mem_germSchedule (selected : package.SelectedGerm) :
    selected ∈ package.germSchedule.values := by
  classical
  rw [germSchedule, Enumeration.ofNodupList_values, Finset.mem_toList,
    List.mem_toFinset]
  unfold SelectedGerm at selected
  rw [List.mem_filterMap]
  refine ⟨selected.1, by simp, ?_⟩
  rw [dif_pos selected.2]

/-- Two scheduled selected coordinates whose actual connector germs are
different.  Difference is stated on the derived paths, so no proof-irrelevant
record inequality can create a false pair. -/
structure GermPair where
  left : package.SelectedGerm
  right : package.SelectedGerm
  different : left.germ.path ≠ right.germ.path

/-- The exact ordered square of the selected-germ schedule, filtered by actual
path inequality. -/
noncomputable def germPairSchedule : Enumeration package.GermPair := by
  classical
  let candidates : List package.GermPair :=
    package.germSchedule.values.flatMap fun left =>
    package.germSchedule.values.filterMap fun right =>
      if different : left.germ.path ≠ right.germ.path then
        some ({ left := left, right := right, different := different } :
          package.GermPair)
      else none
  exact Enumeration.ofNodupList candidates.toFinset.toList
    (Finset.nodup_toList candidates.toFinset)

/-- Completeness of the finite distinct-germ-pair schedule. -/
theorem mem_germPairSchedule (pair : package.GermPair) :
    pair ∈ package.germPairSchedule.values := by
  classical
  rw [germPairSchedule, Enumeration.ofNodupList_values, Finset.mem_toList,
    List.mem_toFinset]
  rw [List.mem_flatMap]
  refine ⟨pair.left, package.mem_germSchedule pair.left, ?_⟩
  rw [List.mem_filterMap]
  refine ⟨pair.right, package.mem_germSchedule pair.right, ?_⟩
  rw [dif_pos pair.different]

namespace GermPair

variable {package : VisibleFourUnpeeledPackage support threshold scale receiver peeled}
variable (pair : package.GermPair)

/-- Ambient vertices at which the two actual germs structurally separate, in
the object's canonical vertex order. -/
noncomputable def separatorOrder : List object.Vertex := by
  classical
  exact object.orderedVertices.filter fun separator =>
    decide (SeparatesAt pair.left.germ.path pair.right.germ.path separator)

/-- The separator order is nonempty because two distinct rooted germs through
the same completion port cannot be prefixes of one another. -/
theorem separatorOrder_ne_nil : pair.separatorOrder ≠ [] := by
  obtain ⟨separator, separates⟩ := exists_separatesAt_of_ne pair.different
  have member : separator ∈ pair.separatorOrder := by
    simp [separatorOrder, object.mem_orderedVertices separator, separates]
  intro empty
  rw [empty] at member
  exact List.not_mem_nil member

/-- The exact structural payload at the lexicographically first separating
vertex.  Boundary readings are intentionally absent. -/
structure FirstSeparator where
  separator : object.Vertex
  remaining : List object.Vertex
  selected : pair.separatorOrder = separator :: remaining
  common : List object.Vertex
  nextLeft : object.Vertex
  nextRight : object.Vertex
  tailLeft : List object.Vertex
  tailRight : List object.Vertex
  leftEq : pair.left.germ.path = common ++ separator :: nextLeft :: tailLeft
  rightEq : pair.right.germ.path = common ++ separator :: nextRight :: tailRight
  distinct : nextLeft ≠ nextRight

/-- Select the first separating vertex and unpack its actual path
decomposition. -/
noncomputable def firstSeparator : pair.FirstSeparator := by
  classical
  apply Classical.choice
  obtain ⟨separator, remaining, selected⟩ :=
    List.exists_cons_of_ne_nil pair.separatorOrder_ne_nil
  have member : separator ∈ pair.separatorOrder := by
    rw [selected]
    exact List.mem_cons_self
  have separates : SeparatesAt pair.left.germ.path pair.right.germ.path
      separator := by
    simpa [separatorOrder, object.mem_orderedVertices separator] using member
  obtain ⟨common, nextLeft, nextRight, tailLeft, tailRight, leftEq, rightEq,
    distinct⟩ := separates
  exact ⟨{
    separator := separator
    remaining := remaining
    selected := selected
    common := common
    nextLeft := nextLeft
    nextRight := nextRight
    tailLeft := tailLeft
    tailRight := tailRight
    leftEq := leftEq
    rightEq := rightEq
    distinct := distinct
  }⟩

/-- The selected vertex really is a structural separator. -/
theorem firstSeparator_separatesAt :
    SeparatesAt pair.left.germ.path pair.right.germ.path
      pair.firstSeparator.separator := by
  exact ⟨pair.firstSeparator.common, pair.firstSeparator.nextLeft,
    pair.firstSeparator.nextRight, pair.firstSeparator.tailLeft,
    pair.firstSeparator.tailRight, pair.firstSeparator.leftEq,
    pair.firstSeparator.rightEq, pair.firstSeparator.distinct⟩

/-- Lex-first normalization is exact: the filtered canonical order begins with
the selected separator. -/
theorem separatorOrder_eq_cons :
    pair.separatorOrder =
      pair.firstSeparator.separator :: pair.firstSeparator.remaining :=
  pair.firstSeparator.selected

end GermPair

end ExitFour.VisibleFourUnpeeledPackage

end

end Hypostructure.Graph
