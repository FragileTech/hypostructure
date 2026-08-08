import Hypostructure.Graph.TypeAVisibleResponseAssembly

namespace Hypostructure.Graph.ExitFour

open Hypostructure

universe u

variable {object : FiniteObject.{u}}
variable {support : Finset object.Vertex} {threshold scale : Nat}
variable {receiver : object.Vertex} {peeled : Finset object.Vertex}

attribute [local instance] vertexDecEq

namespace VisibleFourUnpeeledPackage

example
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :
    (package.selectedPieceChannel load).length =
        (package.selectedResponseCoordinate load).channel.length ∧
      (package.selectedContextConnector load).length =
        (package.selectedResponseCoordinate load).connectorLabel :=
  ⟨package.selectedPieceChannel_length load,
    package.selectedContextConnector_length load⟩

example
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :
    (package.selectedResponseCoordinate load).receiverBoundary.1 = receiver := by
  rfl

end VisibleFourUnpeeledPackage
end Hypostructure.Graph.ExitFour
