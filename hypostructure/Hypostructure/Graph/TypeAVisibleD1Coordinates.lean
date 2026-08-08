import Hypostructure.Graph.TraceCoordinateSystem
import Hypostructure.Graph.TypeAVisibleFourPackage

namespace Hypostructure.Graph.ExitFour

open Hypostructure

universe u

variable {object : FiniteObject.{u}}

attribute [local instance] vertexDecEq

namespace VisibleFourUnpeeledPackage

variable {support : Finset object.Vertex} {threshold scale : Nat}
variable {receiver : object.Vertex} {peeled : Finset object.Vertex}

/-- The first-entry receiver of each selected return lies in the canonical cut
boundary of the selected component. -/
theorem selectedReturn_entry_mem_cutBoundary
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : object.Vertex)
    (member : load ∈ selectedVisibleUnpeeledLoads support threshold scale
      receiver package.outside peeled) :
    (package.selectedReturn load member).entry ∈
      Strategy.InterfaceReplacement.SupportAtom.cutBoundary object support := by
  let return' := package.selectedReturn load member
  have portData :=
    (VisibleEntry.mem_completionPorts (object := object)).mp package.port
  have receiverInside : receiver ∈ support :=
    return'.isChannel.2 receiver return'.channel.end_mem_support
  obtain ⟨entry, firstEntry, entryInside, before, beforeOutside, adjacent,
      _edgeMember⟩ :=
    VisibleEntry.exists_entry_with_outside_neighbour return'.toAnchoredReturn.path
      portData.2 receiverInside
  have canonicalFirst := return'.firstEntry?_toAnchoredReturn
  unfold VisibleEntry.firstEntry? at canonicalFirst
  have entryEq : entry = return'.entry := by
    rw [firstEntry] at canonicalFirst
    exact Option.some.inj canonicalFirst
  subst entry
  exact
    (Strategy.InterfaceReplacement.SupportAtom.mem_cutBoundary_iff object support
      return'.entry).2 ⟨entryInside, before, adjacent.symm, beforeOutside⟩

/-- The canonical D1 boundary-response coordinate of one selected
return/load pair.  Its vertex is the actual first-entry receiver of the
canonical scheduled return. -/
noncomputable def selectedD1Coordinate
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : object.Vertex)
    (member : load ∈ selectedVisibleUnpeeledLoads support threshold scale
      receiver package.outside peeled) :
    TraceCoordinateSystem.D1.Coordinate object support :=
  ⟨(package.selectedReturn load member).entry,
    package.selectedReturn_entry_mem_cutBoundary load member⟩

/-- The exact uncapped D1 value carried by a selected return/load pair. -/
noncomputable def selectedD1Value
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : object.Vertex)
    (member : load ∈ selectedVisibleUnpeeledLoads support threshold scale
      receiver package.outside peeled) : Nat :=
  TraceCoordinateSystem.D1.value object support
    (package.selectedD1Coordinate load member)

/-- The exact singleton declared support of a selected D1 coordinate. -/
noncomputable def selectedD1DeclaredSupport
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : object.Vertex)
    (member : load ∈ selectedVisibleUnpeeledLoads support threshold scale
      receiver package.outside peeled) : Finset object.Vertex :=
  TraceCoordinateSystem.D1.declaredSupport object support
    (package.selectedD1Coordinate load member)

@[simp] theorem selectedD1Coordinate_vertex
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : object.Vertex)
    (member : load ∈ selectedVisibleUnpeeledLoads support threshold scale
      receiver package.outside peeled) :
    (package.selectedD1Coordinate load member).1 =
      (package.selectedReturn load member).entry := rfl

@[simp] theorem selectedD1DeclaredSupport_eq
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : object.Vertex)
    (member : load ∈ selectedVisibleUnpeeledLoads support threshold scale
      receiver package.outside peeled) :
    package.selectedD1DeclaredSupport load member =
      {(package.selectedReturn load member).entry} := rfl

/-- The selected return literally owns its first-entry D1 coordinate. -/
theorem selectedReturn_ownsD1
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : object.Vertex)
    (member : load ∈ selectedVisibleUnpeeledLoads support threshold scale
      receiver package.outside peeled) :
    (package.selectedReturn load member).OwnsBoundaryEntry
      (threshold := threshold) (package.selectedD1Coordinate load member).1 load := by
  let return' := package.selectedReturn load member
  refine ⟨?_, package.selectedReturn_visible load member⟩
  unfold VisibleEntry.ReceiverEntryReturn.toAnchoredReturn
  rw [SimpleGraph.Walk.support_append]
  change {return'.entry} ⊆
    (return'.connector.support ++ return'.channel.support.tail).toFinset
  rw [Finset.singleton_subset_iff, List.mem_toFinset]
  exact List.mem_append_left _ return'.connector.end_mem_support

/-- The selected D1 coordinate is `u`-supported through the actual scheduled
receiver-entry return, with no separately supplied ownership witness. -/
theorem selectedD1_uSupported
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : object.Vertex)
    (member : load ∈ selectedVisibleUnpeeledLoads support threshold scale
      receiver package.outside peeled) :
    TraceCoordinateSystem.D1.USupported object support threshold receiver load
      (package.selectedD1Coordinate load member) := by
  right
  exact VisibleEntry.ownsBoundaryEntry_of_return
    (package.selectedD1Coordinate load member).1 package.port
    (package.selectedReturn load member) (package.selectedReturn_ownsD1 load member)

/-- The finite domain of the selected D1 coordinate map. -/
abbrev SelectedLoad
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled) :=
  {load : object.Vertex //
    load ∈ selectedVisibleUnpeeledLoads support threshold scale receiver
      package.outside peeled}

/-- The canonical map from the selected visible unpeeled loads to their exact
D1 coordinates. -/
noncomputable def selectedD1Map
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled) :
    package.SelectedLoad → TraceCoordinateSystem.D1.Coordinate object support :=
  fun load => package.selectedD1Coordinate load.1 load.2

/-- An actual D1 collision among two distinct selected unpeeled loads. -/
def HasSelectedD1Collision
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled) :
    Prop :=
  ∃ left right : package.SelectedLoad,
    left ≠ right ∧ package.selectedD1Map left = package.selectedD1Map right

/-- The finite structural Q1 split: the canonical selected coordinate map has
an explicit collision, or it is injective on the pairwise-distinct selected
loads.  This decides only equality in the constructed D1 map; it does not test
target defect, compression, or any authored exit proposition. -/
theorem selectedD1Collision_or_injective
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled) :
    package.HasSelectedD1Collision ∨ Function.Injective package.selectedD1Map := by
  classical
  by_cases injective : Function.Injective package.selectedD1Map
  · exact Or.inr injective
  · left
    simp only [Function.Injective, not_forall] at injective
    obtain ⟨left, right, equal, distinct⟩ := injective
    exact ⟨left, right, distinct, equal⟩

end VisibleFourUnpeeledPackage

end Hypostructure.Graph.ExitFour
