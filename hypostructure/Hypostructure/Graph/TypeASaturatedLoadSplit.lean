import Hypostructure.Graph.ExitFourPeeling
import Hypostructure.Graph.VisibleReceiverEntry

namespace Hypostructure.Graph.ExitFour

open Hypostructure
open scoped BigOperators

universe u

variable {object : FiniteObject.{u}}

attribute [local instance] vertexDecEq

/-- The visible routed loads that remain after the selected exit-(4) peeling
set has been removed. -/
noncomputable def unpeeledVisibleLoads
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) :
    Finset object.Vertex :=
  VisibleEntry.visibleLoads object support threshold receiver ∩
    unpeeledLoads support threshold receiver peeled

/-- The visible unpeeled loads seen through one selected completion port. -/
noncomputable def unpeeledVisibleLoadsAt
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver outside : object.Vertex) (peeled : Finset object.Vertex) :
    Finset object.Vertex :=
  VisibleEntry.visibleLoadsAt object support threshold receiver outside ∩
    unpeeledLoads support threshold receiver peeled

/-- The paper's canonical visible-first order, restricted to the unpeeled
routed loads of the selected receiver. -/
noncomputable def unpeeledVisibleFirstOrder
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) :
    List object.Vertex := by
  classical
  exact (object.orderedVertices.filter fun vertex =>
      decide (vertex ∈ unpeeledVisibleLoads support threshold receiver peeled)) ++
    object.orderedVertices.filter fun vertex =>
      decide (vertex ∈ unpeeledLoads support threshold receiver peeled ∧
        vertex ∉ VisibleEntry.visibleLoads object support threshold receiver)

/-- `A₄(w)`: the first `s*q(w)-1` unpeeled loads in visible-first order. -/
noncomputable def unpeeledPayableSet
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) :
    Finset object.Vertex := by
  classical
  exact ((unpeeledVisibleFirstOrder support threshold receiver peeled).take
    (scale * object.missingPorts support threshold receiver - 1)).toFinset

/-- `E₄(w)`: the unpeeled routed loads left after the canonical payable
prefix has been removed. -/
noncomputable def unpeeledExcess
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) :
    Finset object.Vertex :=
  unpeeledLoads support threshold receiver peeled \
    unpeeledPayableSet support threshold scale receiver peeled

/-- A completion port carries the registered overload number of distinct
visible unpeeled routed loads.  In the paper the registered scale is four. -/
def VisibleFourUnpeeledAt
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) : Prop :=
  ∃ outside ∈ VisibleEntry.completionPorts object support receiver,
    scale ≤
      (unpeeledVisibleLoadsAt support threshold receiver outside peeled).card

/-- The complementary paper alternative: no port carries the overload number
of visible unpeeled loads, and the canonical residual excess is nonempty and
entirely silent. -/
def SilentUnpeeledExcessAt
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) : Prop :=
  (∀ outside ∈ VisibleEntry.completionPorts object support receiver,
      (unpeeledVisibleLoadsAt support threshold receiver outside peeled).card + 1
        ≤ scale) ∧
    (unpeeledExcess support threshold scale receiver peeled).Nonempty ∧
    unpeeledExcess support threshold scale receiver peeled ⊆
      unpeeledLoads support threshold receiver peeled \
        VisibleEntry.visibleLoads object support threshold receiver

theorem unpeeledPayableSet_card_le
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) :
    (unpeeledPayableSet support threshold scale receiver peeled).card ≤
      scale * object.missingPorts support threshold receiver - 1 := by
  classical
  refine le_trans (List.toFinset_card_le _) ?_
  simpa [unpeeledPayableSet] using
    (List.length_take_le
      (scale * object.missingPorts support threshold receiver - 1)
      (unpeeledVisibleFirstOrder support threshold receiver peeled))

theorem unpeeledPayableSet_subset
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) :
    unpeeledPayableSet support threshold scale receiver peeled ⊆
      unpeeledLoads support threshold receiver peeled := by
  classical
  intro vertex member
  have inTaken : vertex ∈
      (unpeeledVisibleFirstOrder support threshold receiver peeled).take
        (scale * object.missingPorts support threshold receiver - 1) := by
    simpa [unpeeledPayableSet] using member
  have inOrder : vertex ∈
      unpeeledVisibleFirstOrder support threshold receiver peeled :=
    List.mem_of_mem_take inTaken
  rw [unpeeledVisibleFirstOrder, List.mem_append] at inOrder
  rcases inOrder with visible | silent
  · have visibleMember :
        vertex ∈ unpeeledVisibleLoads support threshold receiver peeled := by
      simpa using visible
    exact Finset.mem_inter.mp visibleMember |>.2
  · have silentMember :
        vertex ∈ unpeeledLoads support threshold receiver peeled ∧
          vertex ∉ VisibleEntry.visibleLoads object support threshold receiver := by
      simpa using silent
    exact silentMember.1

theorem unpeeledVisibleLoads_subset_payableSet
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex)
    (paid : (unpeeledVisibleLoads support threshold receiver peeled).card ≤
      scale * object.missingPorts support threshold receiver - 1) :
    unpeeledVisibleLoads support threshold receiver peeled ⊆
      unpeeledPayableSet support threshold scale receiver peeled := by
  classical
  let visibleBlock := object.orderedVertices.filter fun vertex =>
    decide (vertex ∈ unpeeledVisibleLoads support threshold receiver peeled)
  have blockFinset : visibleBlock.toFinset =
      unpeeledVisibleLoads support threshold receiver peeled := by
    ext vertex
    simp [visibleBlock, object.mem_orderedVertices vertex]
  have blockLength : visibleBlock.length =
      (unpeeledVisibleLoads support threshold receiver peeled).card := by
    rw [← blockFinset, List.toFinset_card_of_nodup
      (object.orderedVertices_nodup.filter _)]
  have takeAll : visibleBlock.take
      (scale * object.missingPorts support threshold receiver - 1) =
      visibleBlock :=
    List.take_of_length_le (by omega)
  intro vertex member
  have inBlock : vertex ∈ visibleBlock := by
    rw [← List.mem_toFinset, blockFinset]
    exact member
  refine List.mem_toFinset.mpr ?_
  unfold unpeeledVisibleFirstOrder
  rw [List.take_append, show
    (object.orderedVertices.filter fun vertex =>
      decide (vertex ∈ unpeeledVisibleLoads support threshold receiver peeled)) =
        visibleBlock from rfl, takeAll]
  exact List.mem_append_left _ inBlock

/-- The exact selected-component saturated-load split used before the eight
receiver exits.  It retains the receiver and peeling set and constructs the
paper's nonempty silent residual excess when no visible port is overloaded. -/
theorem visibleFourUnpeeled_or_silentUnpeeledExcess
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex)
    (exact : object.degree receiver = threshold)
    (isReceiver : object.IsReceiver support threshold receiver)
    (saturated : SaturatedAfter support threshold scale receiver peeled) :
    VisibleFourUnpeeledAt support threshold scale receiver peeled ∨
      SilentUnpeeledExcessAt support threshold scale receiver peeled := by
  classical
  by_cases visible :
      VisibleFourUnpeeledAt support threshold scale receiver peeled
  · exact Or.inl visible
  · right
    have noVisiblePort : ∀ outside ∈
        VisibleEntry.completionPorts object support receiver,
        (unpeeledVisibleLoadsAt support threshold receiver outside peeled).card + 1
          ≤ scale := by
      intro outside port
      have notOverloaded : ¬ scale ≤
          (unpeeledVisibleLoadsAt support threshold receiver outside peeled).card := by
        intro overloaded
        exact visible ⟨outside, port, overloaded⟩
      omega
    have visibleSubset :
        unpeeledVisibleLoads support threshold receiver peeled ⊆
          (VisibleEntry.completionPorts object support receiver).biUnion
            (fun outside => unpeeledVisibleLoadsAt support threshold receiver
              outside peeled) := by
      intro load member
      have visibleMember := Finset.mem_inter.mp member
      obtain ⟨_routed, outside, port, atPort⟩ :=
        (VisibleEntry.mem_visibleLoads object).mp visibleMember.1
      exact Finset.mem_biUnion.mpr
        ⟨outside, port, Finset.mem_inter.mpr ⟨atPort, visibleMember.2⟩⟩
    have visibleCardLeSum :
        (unpeeledVisibleLoads support threshold receiver peeled).card ≤
          ∑ outside ∈ VisibleEntry.completionPorts object support receiver,
            (unpeeledVisibleLoadsAt support threshold receiver outside peeled).card :=
      le_trans (Finset.card_le_card visibleSubset)
        (Finset.card_biUnion_le
          (s := VisibleEntry.completionPorts object support receiver)
          (t := fun outside => unpeeledVisibleLoadsAt support threshold receiver
            outside peeled))
    have portSum :
        ∑ outside ∈ VisibleEntry.completionPorts object support receiver,
            ((unpeeledVisibleLoadsAt support threshold receiver outside peeled).card + 1)
          ≤
        ∑ _outside ∈ VisibleEntry.completionPorts object support receiver,
          scale :=
      Finset.sum_le_sum noVisiblePort
    have ports := VisibleEntry.card_completionPorts object support threshold exact
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, smul_eq_mul,
      smul_eq_mul, Nat.mul_one, ports] at portSum
    rw [Nat.mul_comm (object.missingPorts support threshold receiver) scale] at portSum
    have missingPositive : 1 ≤
        object.missingPorts support threshold receiver := by
      unfold FiniteObject.missingPorts
      have receiverDeficient := isReceiver.2
      omega
    have scalePositive : 1 ≤ scale := by
      have portsNonempty :
          (VisibleEntry.completionPorts object support receiver).Nonempty := by
        rw [← Finset.card_pos, ports]
        exact missingPositive
      obtain ⟨outside, port⟩ := portsNonempty
      have portBound := noVisiblePort outside port
      omega
    have visiblePaid :
        (unpeeledVisibleLoads support threshold receiver peeled).card ≤
          scale * object.missingPorts support threshold receiver - 1 := by
      have bound := Nat.add_le_add_right visibleCardLeSum
        (object.missingPorts support threshold receiver)
      omega
    have visibleInPayable := unpeeledVisibleLoads_subset_payableSet
      support threshold scale receiver peeled visiblePaid
    have excessNonempty :
        (unpeeledExcess support threshold scale receiver peeled).Nonempty := by
      by_contra empty
      rw [Finset.not_nonempty_iff_eq_empty] at empty
      have unpeeledSubsetPayable :
          unpeeledLoads support threshold receiver peeled ⊆
            unpeeledPayableSet support threshold scale receiver peeled := by
        intro load unpeeled
        by_contra unpaid
        have inExcess : load ∈
            unpeeledExcess support threshold scale receiver peeled :=
          Finset.mem_sdiff.mpr ⟨unpeeled, unpaid⟩
        rw [empty] at inExcess
        exact Finset.notMem_empty load inExcess
      have residualBound :
          residualLoad support threshold receiver peeled ≤
            scale * object.missingPorts support threshold receiver - 1 := by
        unfold residualLoad
        exact le_trans (Finset.card_le_card unpeeledSubsetPayable)
          (unpeeledPayableSet_card_le support threshold scale receiver peeled)
      unfold SaturatedAfter at saturated
      omega
    have excessSilent :
        unpeeledExcess support threshold scale receiver peeled ⊆
          unpeeledLoads support threshold receiver peeled \
            VisibleEntry.visibleLoads object support threshold receiver := by
      intro load member
      have excessParts := Finset.mem_sdiff.mp member
      refine Finset.mem_sdiff.mpr ⟨excessParts.1, ?_⟩
      intro visibleLoad
      have unpeeledVisible : load ∈
          unpeeledVisibleLoads support threshold receiver peeled :=
        Finset.mem_inter.mpr ⟨visibleLoad, excessParts.1⟩
      exact excessParts.2 (visibleInPayable unpeeledVisible)
    exact ⟨noVisiblePort, excessNonempty, excessSilent⟩

end Hypostructure.Graph.ExitFour
