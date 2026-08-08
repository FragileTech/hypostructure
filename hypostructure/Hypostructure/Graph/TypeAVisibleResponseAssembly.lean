import Hypostructure.Graph.BoundariedResponseWalkAssembly
import Hypostructure.Graph.TypeAVisibleResponseCoordinate

namespace Hypostructure.Graph

open Hypostructure
open Hypostructure.Graph.BoundariedResponseWalkAssembly

universe u

variable {object : FiniteObject.{u}}

attribute [local instance] vertexDecEq

namespace VisibleEntry.ResponseCoordinate

variable {support : Finset object.Vertex} {receiver : object.Vertex}

/-- The receiver endpoint is itself a label of the canonical cut interface,
because the completion port leaves the selected support. -/
noncomputable def receiverBoundary
    (coordinate : VisibleEntry.ResponseCoordinate object support receiver) :
    Strategy.InterfaceReplacement.SupportAtom.BoundaryVertex object support :=
  ⟨receiver,
    (Strategy.InterfaceReplacement.SupportAtom.mem_cutBoundary_iff
      object support receiver).2 ⟨
        coordinate.isChannel.2 receiver coordinate.channel.end_mem_support,
        coordinate.outside,
        (VisibleEntry.mem_completionPorts.mp coordinate.port).1,
        (VisibleEntry.mem_completionPorts.mp coordinate.port).2⟩⟩

end VisibleEntry.ResponseCoordinate

namespace ExitFour

namespace VisibleFourUnpeeledPackage

variable {support : Finset object.Vertex} {threshold scale : Nat}
variable {receiver : object.Vertex} {peeled : Finset object.Vertex}

noncomputable def selectedChannelOwnedWalk
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :
    BoundariedResponseWalkAssembly.SupportAtom.AtomOwnedWalk object support
      (start := (package.selectedReturn load.1 load.2).entry)
      (finish := receiver) :=
  ⟨(package.selectedReturn load.1 load.2).channel,
    (package.selectedReturn load.1 load.2).isChannel.2⟩

noncomputable def selectedConnectorContextEntryWalk
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :
    BoundariedResponseWalkAssembly.SupportAtom.ContextEntryWalk object support
      (start := package.outside)
      (entry := (package.selectedReturn load.1 load.2).entry) :=
  ⟨(package.selectedResponseCoordinate load).connector,
    (package.selectedResponseCoordinate load).entry.2,
    (package.selectedResponseCoordinate load).connectorOutside⟩

/-- The actual channel assembled in the canonical atom-side graph. -/
noncomputable def selectedPieceChannel
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :=
  (package.selectedChannelOwnedWalk load).inPiece

/-- The actual connector assembled in the canonical outside-context graph. -/
noncomputable def selectedContextConnector
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :=
  (package.selectedConnectorContextEntryWalk load).inContext

@[simp] theorem selectedPieceChannel_length
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :
    (package.selectedPieceChannel load).length =
      (package.selectedResponseCoordinate load).channel.length := by
  rw [selectedPieceChannel,
    BoundariedResponseWalkAssembly.SupportAtom.AtomOwnedWalk.inPiece_length]
  rfl

@[simp] theorem selectedContextConnector_length
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :
    (package.selectedContextConnector load).length =
      (package.selectedResponseCoordinate load).connectorLabel := by
  rw [selectedContextConnector,
    BoundariedResponseWalkAssembly.SupportAtom.ContextEntryWalk.inContext_length]
  rfl

end VisibleFourUnpeeledPackage

end ExitFour
end Hypostructure.Graph
