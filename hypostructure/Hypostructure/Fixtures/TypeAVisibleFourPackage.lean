import Hypostructure.Graph.TypeAVisibleFourPackage

namespace Hypostructure.Fixtures.TypeAVisibleFourPackage

open Hypostructure.Graph

universe u

example {object : FiniteObject.{u}} (support : Finset object.Vertex)
    (threshold scale : Nat) (receiver : object.Vertex)
    (peeled : Finset object.Vertex)
    (visible : ExitFour.VisibleFourUnpeeledAt support threshold scale receiver
      peeled) :
    Nonempty
      (ExitFour.VisibleFourUnpeeledPackage support threshold scale receiver
        peeled) :=
  ExitFour.visibleFourUnpeeledPackage support threshold scale receiver peeled
    visible

end Hypostructure.Fixtures.TypeAVisibleFourPackage
