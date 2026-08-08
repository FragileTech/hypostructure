import Hypostructure.Graph.TypeAVisibleResponseCoordinate

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
    (package.selectedResponseCoordinate load).connectorLabel =
        (package.selectedReturn load.1 load.2).connector.length ∧
      (package.selectedResponseCoordinate load).connector =
        (package.selectedReturn load.1 load.2).connector ∧
      (package.selectedResponseCoordinate load).entry.1 =
        (package.selectedReturn load.1 load.2).entry ∧
      (package.selectedResponseCoordinate load).channel =
        (package.selectedReturn load.1 load.2).channel :=
  ⟨package.selectedResponseCoordinate_connectorLabel load,
    package.selectedResponseCoordinate_connector load,
    package.selectedResponseCoordinate_entry load,
    package.selectedResponseCoordinate_channel load⟩

example
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :
    (∀ vertex ∈ (package.selectedReturn load.1 load.2).connector.support,
      vertex ≠ (package.selectedResponseCoordinate load).entry.1 →
        vertex ∉ support) ∧
      VisibleEntry.IsChannel object support
        (package.selectedResponseCoordinate load).channel :=
  package.selectedResponseCoordinate_ownership load

example
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (pair : package.Q1OriginPair) :
    pair.leftResponseCoordinate.registeredBoundaryDegreeProfile =
      pair.rightResponseCoordinate.registeredBoundaryDegreeProfile :=
  pair.responseCoordinates_same_registered_fibre

end VisibleFourUnpeeledPackage
end Hypostructure.Graph.ExitFour
