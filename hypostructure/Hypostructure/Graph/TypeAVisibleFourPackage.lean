import Hypostructure.Graph.TypeASaturatedLoadSplit

namespace Hypostructure.Graph.ExitFour

open Hypostructure

universe u

variable {object : FiniteObject.{u}}

attribute [local instance] vertexDecEq

/-- The overloaded completion ports in the object's canonical vertex order. -/
noncomputable def overloadedPortOrder
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) :
    List object.Vertex := by
  classical
  exact object.orderedVertices.filter fun outside =>
    decide (outside ∈ VisibleEntry.completionPorts object support receiver ∧
      scale ≤
        (unpeeledVisibleLoadsAt support threshold receiver outside peeled).card)

/-- The first registered-overload-many visible unpeeled loads at a port, in
the object's canonical vertex order.  At the paper presentation `scale = 4`. -/
noncomputable def selectedVisibleUnpeeledLoads
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver outside : object.Vertex) (peeled : Finset object.Vertex) :
    List object.Vertex := by
  classical
  exact (object.orderedVertices.filter fun load =>
    decide (load ∈
      unpeeledVisibleLoadsAt support threshold receiver outside peeled)).take scale

/-- The scheduled visible returns for one selected load, in the canonical
finite receiver-entry-return order. -/
noncomputable def visibleReturnOrder
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver outside load : object.Vertex) :
    List (VisibleEntry.ReceiverEntryReturn object support receiver outside) := by
  classical
  exact (VisibleEntry.ReceiverEntryReturn.schedule object support receiver outside).values.filter
    fun return' => decide (VisibleEntry.VisibleFor object support threshold return' load)

/-- The exact selected response-coordinate datum entering the paper's visible
routing lemma.  Every choice is pinned to an existing finite canonical order:
the first overloaded port, the first `scale` visible unpeeled loads, and the
first scheduled visible return for each selected load. -/
structure VisibleFourUnpeeledPackage
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) where
  outside : object.Vertex
  remainingPorts : List object.Vertex
  selectedPort :
    overloadedPortOrder support threshold scale receiver peeled =
      outside :: remainingPorts
  loadCount :
    (selectedVisibleUnpeeledLoads support threshold scale receiver outside
      peeled).length = scale
  loadNodup :
    (selectedVisibleUnpeeledLoads support threshold scale receiver outside
      peeled).Nodup
  selectedReturn : (load : object.Vertex) →
    load ∈ selectedVisibleUnpeeledLoads support threshold scale receiver
      outside peeled →
      VisibleEntry.ReceiverEntryReturn object support receiver outside
  remainingReturns : (load : object.Vertex) →
    (member : load ∈ selectedVisibleUnpeeledLoads support threshold scale
      receiver outside peeled) →
      List (VisibleEntry.ReceiverEntryReturn object support receiver outside)
  selectedReturn_eq : ∀ (load : object.Vertex)
      (member : load ∈ selectedVisibleUnpeeledLoads support threshold scale
        receiver outside peeled),
    visibleReturnOrder support threshold receiver outside load =
      selectedReturn load member :: remainingReturns load member
  selectedReturn_scheduled : ∀ (load : object.Vertex)
      (member : load ∈ selectedVisibleUnpeeledLoads support threshold scale
        receiver outside peeled),
    selectedReturn load member ∈
      (VisibleEntry.ReceiverEntryReturn.schedule object support receiver
        outside).values
  selectedReturn_visible : ∀ (load : object.Vertex)
      (member : load ∈ selectedVisibleUnpeeledLoads support threshold scale
        receiver outside peeled),
    VisibleEntry.VisibleFor object support threshold (selectedReturn load member)
      load

namespace VisibleFourUnpeeledPackage

variable {support : Finset object.Vertex} {threshold scale : Nat}
variable {receiver : object.Vertex} {peeled : Finset object.Vertex}

theorem port
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled) :
    package.outside ∈ VisibleEntry.completionPorts object support receiver := by
  have member : package.outside ∈
      overloadedPortOrder support threshold scale receiver peeled := by
    rw [package.selectedPort]
    exact List.mem_cons_self
  have data :
      package.outside ∈ VisibleEntry.completionPorts object support receiver ∧
        scale ≤ (unpeeledVisibleLoadsAt support threshold receiver
          package.outside peeled).card := by
    simpa [overloadedPortOrder, object.mem_orderedVertices package.outside] using
      member
  exact data.1

theorem overloaded
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled) :
    scale ≤
      (unpeeledVisibleLoadsAt support threshold receiver package.outside
        peeled).card := by
  have member : package.outside ∈
      overloadedPortOrder support threshold scale receiver peeled := by
    rw [package.selectedPort]
    exact List.mem_cons_self
  have data :
      package.outside ∈ VisibleEntry.completionPorts object support receiver ∧
        scale ≤ (unpeeledVisibleLoadsAt support threshold receiver
          package.outside peeled).card := by
    simpa [overloadedPortOrder, object.mem_orderedVertices package.outside] using
      member
  exact data.2

theorem load_mem
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    {load : object.Vertex}
    (member : load ∈ selectedVisibleUnpeeledLoads support threshold scale
      receiver package.outside peeled) :
    load ∈ unpeeledVisibleLoadsAt support threshold receiver package.outside
      peeled := by
  unfold selectedVisibleUnpeeledLoads at member
  have inOrder := List.mem_of_mem_take member
  simpa [object.mem_orderedVertices load] using inOrder

end VisibleFourUnpeeledPackage

/-- A selected overloaded port canonically supplies the finite package of
pairwise-distinct visible unpeeled loads and their first scheduled visible
returns. -/
theorem visibleFourUnpeeledPackage
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex)
    (visible : VisibleFourUnpeeledAt support threshold scale receiver peeled) :
    Nonempty
      (VisibleFourUnpeeledPackage support threshold scale receiver peeled) := by
  classical
  obtain ⟨witnessPort, witnessPortMember, witnessOverloaded⟩ := visible
  have witnessInOrder : witnessPort ∈
      overloadedPortOrder support threshold scale receiver peeled := by
    simp [overloadedPortOrder, object.mem_orderedVertices witnessPort,
      witnessPortMember, witnessOverloaded]
  have portOrderNonempty :
      overloadedPortOrder support threshold scale receiver peeled ≠ [] := by
    intro empty
    rw [empty] at witnessInOrder
    exact List.not_mem_nil witnessInOrder
  obtain ⟨outside, remainingPorts, selectedPort⟩ :=
    List.exists_cons_of_ne_nil portOrderNonempty
  have outsideInOrder : outside ∈
      overloadedPortOrder support threshold scale receiver peeled := by
    rw [selectedPort]
    exact List.mem_cons_self
  have outsideData :
      outside ∈ VisibleEntry.completionPorts object support receiver ∧
        scale ≤
          (unpeeledVisibleLoadsAt support threshold receiver outside peeled).card := by
    simpa [overloadedPortOrder, object.mem_orderedVertices outside] using
      outsideInOrder
  let fullLoadOrder := object.orderedVertices.filter fun load =>
    decide (load ∈
      unpeeledVisibleLoadsAt support threshold receiver outside peeled)
  have fullLoadOrderNodup : fullLoadOrder.Nodup := by
    exact object.orderedVertices_nodup.filter _
  have fullLoadOrderFinset : fullLoadOrder.toFinset =
      unpeeledVisibleLoadsAt support threshold receiver outside peeled := by
    ext load
    simp [fullLoadOrder, object.mem_orderedVertices load]
  have fullLoadOrderLength : fullLoadOrder.length =
      (unpeeledVisibleLoadsAt support threshold receiver outside peeled).card := by
    rw [← fullLoadOrderFinset,
      List.toFinset_card_of_nodup fullLoadOrderNodup]
  have loadCount :
      (selectedVisibleUnpeeledLoads support threshold scale receiver outside
        peeled).length = scale := by
    unfold selectedVisibleUnpeeledLoads
    rw [show
      (object.orderedVertices.filter fun load =>
        decide (load ∈
          unpeeledVisibleLoadsAt support threshold receiver outside peeled)) =
        fullLoadOrder from rfl, List.length_take, fullLoadOrderLength]
    omega
  have loadNodup :
      (selectedVisibleUnpeeledLoads support threshold scale receiver outside
        peeled).Nodup := by
    unfold selectedVisibleUnpeeledLoads
    exact (List.take_sublist scale fullLoadOrder).nodup fullLoadOrderNodup
  have selectedLoadMem : ∀ load,
      load ∈ selectedVisibleUnpeeledLoads support threshold scale receiver
        outside peeled →
        load ∈ unpeeledVisibleLoadsAt support threshold receiver outside peeled := by
    intro load member
    unfold selectedVisibleUnpeeledLoads at member
    have inOrder := List.mem_of_mem_take member
    simpa [object.mem_orderedVertices load] using inOrder
  have firstReturnExists : ∀ (load : object.Vertex)
      (member : load ∈ selectedVisibleUnpeeledLoads support threshold scale
        receiver outside peeled),
      ∃ return' remaining,
        visibleReturnOrder support threshold receiver outside load =
          return' :: remaining := by
    intro load member
    have atPort := Finset.mem_inter.mp (selectedLoadMem load member) |>.1
    have visibleWitness : ∃ return' :
        VisibleEntry.ReceiverEntryReturn object support receiver outside,
        VisibleEntry.VisibleFor object support threshold return' load := by
      simpa [VisibleEntry.visibleLoadsAt] using
        (Finset.mem_filter.mp atPort).2
    obtain ⟨return', returnVisible⟩ := visibleWitness
    have returnInOrder : return' ∈
        visibleReturnOrder support threshold receiver outside load := by
      simp [visibleReturnOrder, return'.mem_schedule, returnVisible]
    have orderNonempty :
        visibleReturnOrder support threshold receiver outside load ≠ [] := by
      intro empty
      rw [empty] at returnInOrder
      exact List.not_mem_nil returnInOrder
    exact List.exists_cons_of_ne_nil orderNonempty
  choose selectedReturn remainingReturns selectedReturn_eq using firstReturnExists
  have selectedReturnData : ∀ (load : object.Vertex)
      (member : load ∈ selectedVisibleUnpeeledLoads support threshold scale
        receiver outside peeled),
      selectedReturn load member ∈
          (VisibleEntry.ReceiverEntryReturn.schedule object support receiver
            outside).values ∧
        VisibleEntry.VisibleFor object support threshold
          (selectedReturn load member) load := by
    intro load member
    have firstMember : selectedReturn load member ∈
        visibleReturnOrder support threshold receiver outside load := by
      rw [selectedReturn_eq load member]
      exact List.mem_cons_self
    simpa [visibleReturnOrder] using firstMember
  exact ⟨{
    outside := outside
    remainingPorts := remainingPorts
    selectedPort := selectedPort
    loadCount := loadCount
    loadNodup := loadNodup
    selectedReturn := selectedReturn
    remainingReturns := remainingReturns
    selectedReturn_eq := selectedReturn_eq
    selectedReturn_scheduled := fun load member =>
      (selectedReturnData load member).1
    selectedReturn_visible := fun load member =>
      (selectedReturnData load member).2 }⟩

end Hypostructure.Graph.ExitFour
