import Hypostructure.Graph.TypeAVisibleD1Coordinates

namespace Hypostructure.Fixtures.TypeAVisibleD1Coordinates

open Hypostructure.Graph

universe u

example {object : FiniteObject.{u}} {support : Finset object.Vertex}
    {threshold scale : Nat} {receiver : object.Vertex}
    {peeled : Finset object.Vertex}
    (package : ExitFour.VisibleFourUnpeeledPackage support threshold scale
      receiver peeled) :
    package.HasSelectedD1Collision ∨ Function.Injective package.selectedD1Map :=
  package.selectedD1Collision_or_injective

example {object : FiniteObject.{u}} {support : Finset object.Vertex}
    {threshold scale : Nat} {receiver : object.Vertex}
    {peeled : Finset object.Vertex}
    (package : ExitFour.VisibleFourUnpeeledPackage support threshold scale
      receiver peeled)
    (load : object.Vertex)
    (member : load ∈ ExitFour.selectedVisibleUnpeeledLoads support threshold
      scale receiver package.outside peeled) :
    TraceCoordinateSystem.D1.USupported object support threshold receiver load
      (package.selectedD1Coordinate load member) :=
  package.selectedD1_uSupported load member

end Hypostructure.Fixtures.TypeAVisibleD1Coordinates
