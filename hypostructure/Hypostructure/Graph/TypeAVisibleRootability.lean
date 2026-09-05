import Hypostructure.Graph.TypeAExitSevenGermSchedule

/-!
# Rootability of selected visible receiver-entry returns

Every selected load of a `VisibleFourUnpeeledPackage` is full in the support,
whereas its receiver has deficient internal degree.  Consequently the load is
not the receiver.  Visibility then prevents the selected response channel from
being the zero-length channel at the receiver.  Its first entry is therefore
different from the receiver, and the connector-outside clause makes the
connector disjoint from the receiver.  Thus no selected return is lost by the
rootability filter used by the exit-(7) germ schedule.
-/

namespace Hypostructure.Graph.ExitFour.VisibleFourUnpeeledPackage

open Hypostructure
open Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}}
variable {support : Finset object.Vertex} {threshold scale : Nat}
variable {receiver : object.Vertex} {peeled : Finset object.Vertex}

attribute [local instance] vertexDecEq

/-- A selected visible return cannot revisit its receiver in the outside
connector, so it canonically defines a rooted connector germ. -/
theorem selectedReturn_rootable
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : object.Vertex)
    (member : load ∈ selectedVisibleUnpeeledLoads support threshold scale receiver
      package.outside peeled) :
    (package.selectedReturn load member).Rootable := by
  classical
  let return' := package.selectedReturn load member
  have routed : load ∈ object.routedLoads support threshold receiver := by
    have selected := package.load_mem member
    unfold unpeeledVisibleLoadsAt at selected
    have unpeeled := (Finset.mem_inter.mp selected).2
    exact (Finset.mem_sdiff.mp unpeeled).1
  have routedSpec := object.mem_routedLoads.mp routed
  have receiverInside : receiver ∈ support :=
    return'.isChannel.2 receiver return'.channel.end_mem_support
  have loadNeReceiver : load ≠ receiver := by
    intro equal
    have traceTo := object.traceTo_of_traceReceiver?_eq_some routedSpec.2.2
    have receiverLow : object.internalDegree support receiver < threshold :=
      traceTo.choose_spec.2.2.2
    rw [equal] at routedSpec
    omega
  have entryNeReceiver : return'.entry ≠ receiver := by
    intro equal
    have channelNil : return'.channel.Nil :=
      return'.isChannel.1.nil_iff_eq.mpr equal
    obtain ⟨trace, _selected, visible⟩ :=
      package.selectedReturn_visible load member
    rcases visible with suffix | ⟨terminalEdge, _traceLast, canonical⟩
    · apply loadNeReceiver
      have loadMem : load ∈ return'.channel.support :=
        suffix.mem trace.1.start_mem_support
      rw [SimpleGraph.Walk.nil_iff_support_eq.mp channelNil] at loadMem
      simpa [equal] using loadMem
    · unfold VisibleEntry.canonicalChannel? at canonical
      have accepted := List.find?_some canonical
      simp only [decide_eq_true_eq] at accepted
      have edgeEmpty : return'.channel.edges = [] :=
        SimpleGraph.Walk.edges_eq_nil.mpr channelNil
      rw [edgeEmpty] at accepted
      simp at accepted
  unfold VisibleEntry.ReceiverEntryReturn.Rootable
  intro receiverMem
  exact return'.connectorOutside receiver receiverMem
    (fun equal => entryNeReceiver equal.symm) receiverInside

/-- Every selected load occurs in the exact finite germ schedule; the schedule's
rootability filter removes no member of the visible package. -/
noncomputable def selectedGermOfLoad
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) : package.SelectedGerm :=
  ⟨load, package.selectedReturn_rootable load.1 load.2⟩

theorem selectedGermOfLoad_mem_schedule
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :
    package.selectedGermOfLoad load ∈ package.germSchedule.values :=
  package.mem_germSchedule (package.selectedGermOfLoad load)

end Hypostructure.Graph.ExitFour.VisibleFourUnpeeledPackage
