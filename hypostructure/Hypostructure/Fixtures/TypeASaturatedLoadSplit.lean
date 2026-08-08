import Hypostructure.Graph.TypeASaturatedLoadSplit

namespace Hypostructure.Fixtures.TypeASaturatedLoadSplit

open Hypostructure.Graph

universe u

example {object : FiniteObject.{u}} (support : Finset object.Vertex)
    (threshold scale : Nat) (receiver : object.Vertex)
    (peeled : Finset object.Vertex)
    (exact : object.degree receiver = threshold)
    (isReceiver : object.IsReceiver support threshold receiver)
    (saturated : ExitFour.SaturatedAfter support threshold scale receiver peeled) :
    ExitFour.VisibleFourUnpeeledAt support threshold scale receiver peeled ∨
      ExitFour.SilentUnpeeledExcessAt support threshold scale receiver peeled :=
  ExitFour.visibleFourUnpeeled_or_silentUnpeeledExcess
    support threshold scale receiver peeled exact isReceiver saturated

end Hypostructure.Fixtures.TypeASaturatedLoadSplit
